(*======================================================================

Utilities for dealing with file paths.

=======================================================================*)

structure Paths = struct

fun dbgPrint (s:string) = () (** only enable debugging prints if needed **)

val current_file = ref("")

val current_mod_path: Symbol.symbol list ref = ref([])

val is_unix = (String.sub(OS.FileSys.getDir(),0) = #"/")

val athena_home_option = OS.Process.getEnv("ATHENA_HOME")

val athena_home = 
        (case athena_home_option of 
            NONE => ""
          | (SOME d) => d)

fun findSlash(p) = 
   let fun loop([]) = NONE
         | loop(x::rest) = if x = #"/" orelse x = #"\\" then SOME(x) else loop(rest)
   in
     loop(explode p)
   end

fun adjustSlashesBasedOnSecond(p1,p2) = 
  (case findSlash(p2) of
      NONE => p1
    | SOME(slash) => 
        let val L = explode(p1)
            val L' = map (fn x => if x = #"/" orelse x = #"\\" then slash else x) L
        in
           implode(L')
        end)

fun makePath(p1,p2) = 
      let val p2' = adjustSlashesBasedOnSecond(p2,p1)
      in
         OS.Path.concat(p1,p2')
      end

fun getDirPath(str:string) = #dir (OS.Path.splitDirFile str)
	       
val tmp_dir = ref "."

val open_mod_paths: Symbol.symbol list list ref = ref [[]]

val open_mod_directives: Symbol.symbol list list ref = ref [[]]

val root = 
      let fun loop(str) = let val d = #dir(OS.Path.splitDirFile(str))
                          in if d = str then d else loop(d)
                          end        
      in OS.Path.mkCanonical(loop(OS.FileSys.getDir()))
      end

fun createTempDir () =
    let val tmp_dir_exists = (OS.FileSys.isDir (!tmp_dir)) handle _ => false
    in
	if tmp_dir_exists then ()
    else OS.FileSys.mkDir((!tmp_dir)) 
         handle _ => 
            let val msg = "Cannot create temp dir '" ^ (!tmp_dir) ^ "', reverting to current directory.\n"
            in (print msg; tmp_dir := ".")
            end
    end

fun makeTemp (name:string) = makePath ((!tmp_dir), name)

fun spass_input_file idx = makeTemp("sp.i."^idx)
fun spass_output_file idx = makeTemp("sp.o."^idx)
fun spass_error_file idx = makeTemp("sp.e."^idx)
    
fun fof_file idx = makeTemp("fof.fl."^idx)
fun cnf_file idx = makeTemp("cnf.fl."^idx)
fun cnf_error_file idx = makeTemp("cnf.e.fl."^idx)
    
fun vampireInName(index) = makeTemp("vamp.in."^index)
fun vampireErrorName(index) = makeTemp("vamp.e."^index)
fun vampireOutName(index) = makeTemp("vamp.o."^index)
    
fun eInName(index) = makeTemp("e.in."^index)
fun eOutName(index) = makeTemp("e.o."^index)
    
fun paradoxInName(index) = makeTemp("paradox.in."^index)
fun paradoxOutName(index) = makeTemp("paradox.o."^index)
			                   
(*
   List of "root" directories used for loading Athena files.
   Order is important as a lookup proceeds from left-to-right
   or head-to-tail through the list. New roots are added with the 
   add-path directive.
*)

val (athena_roots:string list ref) = ref []

(* 
   findFile(file_name) returns a string option for the first 
   occurrence of file_name in the list roots of file system 
   roots. If SOME(f) is returned then f is the absolute canonical
   path for file. Otherwise file does not exist and NONE is returned. 
*)

fun findFile(file_name) = 
  let fun findFirstOccurrenceOf(file, []) = NONE
        | findFirstOccurrenceOf(file, root::more) =
             let val path = makePath(root, file)
       	         val _ = dbgPrint ("  -- Checking '" ^ path ^ "'\n")
             in
	       SOME(OS.FileSys.fullPath(path)) 
             end handle SysErr => findFirstOccurrenceOf(file, more)
      val current_dir = getDirPath(!current_file)
  in 
     (SOME(OS.FileSys.fullPath(makePath(current_dir,file_name))))
        handle _ => (SOME(OS.FileSys.fullPath(makePath(athena_home,file_name)))
                       handle _ => (findFirstOccurrenceOf (file_name,!athena_roots)))
       
  end

fun findFileWithPossibleSuffix(file_name,suffix) = 
   (case findFile(file_name) of   
       NONE => findFile(file_name ^ suffix)
     | res => res)

fun findWithPossibleSuffixIterated([],final) = final
  | findWithPossibleSuffixIterated((file_name,suffix)::more,final) =
       (case findFileWithPossibleSuffix(file_name,suffix) of
          SOME(str) => str
	| _ => findWithPossibleSuffixIterated(more,final))

fun findIterated([],final) = final
  | findIterated(file_name::more,final) =
       (case findFile(file_name) of
          SOME(str) => str
	| _ => findIterated(more,final)) 
  
exception InvalidPath of string

(**
addPath(path:string) adds path to the list of roots
provided that path names a valid directory in the file system.
On success the canonical path is returned. Otherwise SysErr
is raised with an error message.
**)

fun addPath path =
    let val fullDirName = OS.FileSys.fullPath path
	val _ = dbgPrint ("  -- addPath '" ^ fullDirName ^ "'\n")
    in
	if OS.FileSys.isDir fullDirName
	then (athena_roots := fullDirName :: (!athena_roots);
	      fullDirName)
	else raise (InvalidPath ("Cannot add path \"" ^ fullDirName ^ "\" (not a directory)"))
    end
    handle OS.SysErr(msg, _) => raise (InvalidPath ("Cannot add path \"" ^ path ^ "\" (" ^ msg ^ ")"))
fun popPath () =
    case (!athena_roots)
	 of [] => dbgPrint ("Paths.popPath() invoked with empty search paths.")
	  | _::xs => athena_roots := xs

(*
   findFileWithName(name:string) searches for a file in the file system
   {r/name | r \in !athena_roots} provided that name is relative. Otherwise, name
   is an absolute path and the canonical absolute path to which name refers is returned.
*)
 
fun findFileWithName (name) =
    let val res = if OS.Path.isRelative name then findFile(name)
                  else SOME(OS.FileSys.fullPath name)
                  	 handle OS.SysErr(msg, _) => (print (msg ^ "\n"); NONE)
        val _ = case res of SOME(s) => () | _ => print("\nNot found!\n")
    in
      res
    end

(*
   Add $ATHENA_HOME/lib and $ATHENA_HOME/lib/basic to search path if $ATHENA_HOME is defined.
*)

fun addAthenaHomePaths (athena_home:string) =
    let val athena_home_lib = addPath (makePath (athena_home, "lib"))
	val _ = addPath (makePath (athena_home_lib, "basic"))
        val _ = addPath (makePath (athena_home_lib, "main"))
    in ()
    end
    handle (InvalidPath msg) => print ("\n" ^ msg ^ "\nIs ATHENA_HOME set correctly?")

val athena_home_option = OS.Process.getEnv("ATHENA_HOME")

val _ = (case athena_home_option of 
            NONE => print("\nWARNING: Environment variable ATHENA_HOME is not set.\n")
          | (SOME d) => (addAthenaHomePaths d;
                         tmp_dir := (makePath (d, "tmp"))))

end  (* of structure Paths *)

