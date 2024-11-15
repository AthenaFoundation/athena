structure AthenaServer = 

struct 

open TopEnv;

open TextIO

structure SU = SockUtil

fun processString(str) = 
     let val _ = print("\nInside processString, incoming request:\n" ^ str ^ "\n")
         val res = TopEnv.processPhraseDirectlyFromString(str,Semantics.top_val_env)
         val _ = print("\nInside processString, resulting value string:\n" ^ res ^ "\n")
     in
        res
     end

val max_bytes_at_once = 1024 * 80

(*======================================================================================================
The readAllSimple function is straightforward and does not require encoding the length of the payload into
the first 4 bytes of the client's request. It is, however, predicated on the assumption that the client will 
shut down the connection after transmitting the payload. Thus, a "natural EOF" can be detected on the server 
side simply when Socket.recvVec returns a vector of length 0, at which point we know that the entire payload 
has been received. This is clean and efficient (esp. with a large value of max_bytes_at_once, but again, 
it does require the client to close the connection after each send. This means that there are no persistent 
socket connections, which is fine for the use cases envisioned here (remote code execution). 

** Important Note: If readAllSimple is used instead of readAll, then the corresponding sending function on 
the Python client side should be send_request_to_server_simple (rather than send_request_to_server), to
ensure that the client does not encode the length of the payload into the first 4 bytes. 
======================================================================================================*)

fun readAllSimple(conn) = 
    let fun loop(vector_list,iteration) = 
  	           let val in_vector = Socket.recvVec(conn,max_bytes_at_once)
	               val len = Word8Vector.length(in_vector)
   	           in
                      (* Connection is closed, end of message reached *) 
                      if len = 0 then rev(in_vector::vector_list)
                      else loop(in_vector::vector_list,iteration+1)
                   end
	val vector_list = loop([],1)
     in
        Byte.bytesToString(Word8Vector.concat(vector_list))
     end;

fun readExactly(conn, n) =
    let fun loop(acc_list, bytes_read) =
            if bytes_read >= n
            then rev(acc_list)
            else
                let val vec = Socket.recvVec(conn, n - bytes_read)
                    val len = Word8Vector.length(vec)
                in
                    if len = 0 
                    then Basic.fail("Premature connection closure, unable to extract the length of the payload from the first 4 bytes.")
                    else loop(vec::acc_list, bytes_read + len)
                end
    in
      Word8Vector.concat(loop([], 0))
    end

(*======================================================================================================
This implementation of readAll assumes that the client has encoded the length of the actual payload into
the first 4 bytes of the request. (This means that the largest possible payload that a client can send to
an Athena TCP server has a size that can be represented by 4 bytes; that comes to roughly 4 gigabytes.) 

Since TCP might break up a message into arbitrarily many chunks, it's conceivable (though extremely unlikely)
that even the first 4 bytes of the incoming request are broken up into more that one part (e.g., 2 bytes and
then another 2 bytes). For that reason, readExactly is used to extract the first 4 bytes (though this is 
likely overkill; in the vast majority of cases, the internal loop of readExactly should only perform 
one single iteration). 

======================================================================================================*)

fun readAll(conn) = 
    let val length_vec = readExactly(conn,4)
        (******)
        val _ = print("\nReceived length bytes: ") 
        val _ = Word8Vector.app (fn b => print(Int.toString(Word8.toInt b) ^ " "))
                                length_vec
        (******)
        (****** 
        Now do the exact inverse of what the client is expected to do: 
        ******)
	val expected_length = Word8Vector.foldl (fn (b, acc) => acc * 256 + Word8.toInt b) 
                                                0 
                                                length_vec
        (******)
        val _ = print("\nExpected length: " ^ Int.toString expected_length)
        (******)
        fun loop(vector_list, bytes_read) = 
            if bytes_read >= expected_length 
            then rev(vector_list)
            else 
                let val in_vector = Socket.recvVec(conn, Int.min(max_bytes_at_once, expected_length - bytes_read))
                    val len = Word8Vector.length(in_vector)
                    (******) 
                     val _ = print("\nReceived chunk of length: " ^ Int.toString len)  
                    (******)
                in
                  loop(in_vector::vector_list, bytes_read + len)
                end
    in
      Byte.bytesToString(Word8Vector.concat(loop([], 0)))
    end

fun acceptLoop(server_port:int) =
    let fun respond(conn) = 
               let val request_text = readAll(conn)
  	           val reply = processString(request_text)
		   val _ = SU.sendStr(conn,reply)
               in
	          Socket.close(conn)
               end handle x => (Socket.close(conn);raise x)
        fun accept(listener) = 
              let val (conn,conn_addr) = Socket.accept(listener)
		  val _ = Thread.spawn(fn () => (respond(conn); ()))
              in
                 accept(listener)
              end
	val listener = INetSock.TCP.socket()
	val _ = INetSock.TCP.setNODELAY(listener,true)	
        val _ = Socket.Ctl.setREUSEADDR(listener,true);
    in
          Socket.bind(listener,INetSock.any server_port);
          Socket.listen(listener,9);
          accept(listener)
    end

fun startServer(port,file_name_option) = 
    let val sock = INetSock.TCP.socket()
    	val _ = Repl.init(file_name_option)
    in
      print "\nEntering accept loop...\n";
      acceptLoop(port)
    end

fun noisy(f) = 
   fn () => 
    (let val () = f()
    handle e => 
       let val () = TextIO.print ("Exception: " ^ (exnName e)
         ^ " Message: " ^ (exnMessage e) ^ "\n")
        in RunCML.shutdown(OS.Process.failure) end
     in RunCML.shutdown(OS.Process.success)
    end)

end;

