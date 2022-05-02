(*======================================================================

A structure implementing some basic functionality for working with positions

=======================================================================*)

structure Position = 

struct

val accum = ref(0);

val eof = ref(false);

fun save() = ();

fun init()= ();

val line_num = ref(1);

val file_name = ref "";

val pos = ref(1);

type PosType = {line:int,pos:int,file:string};         

fun incPos({line,file,pos}) = {line=line,file=file,pos=pos+1};

fun posToString({file,line,pos}:PosType) = file^":"^Int.toString(line)^":"^Int.toString(pos);

val dummy_pos:PosType = {file=Names.top_level_name,line=0,pos=0};

fun newLine(yypos)= (Basic.inc(line_num); 
                     accum := !accum + (yypos - !accum));

fun lexCompare(p1:PosType as {line=line1,pos=pos1,...},
               p2:PosType as {line=line2,pos=pos2,...}) = 
     (line1 < line2) orelse (line1 = line2 andalso pos1 < pos2);

fun getPos(yypos) = 
    let val p:PosType = {line=(!line_num),file=(!file_name),pos=yypos-(!accum)} 
    in 
       p 
    end;

end; 
