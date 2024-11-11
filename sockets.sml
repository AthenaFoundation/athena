(*======================================================================

This is a self-contained SML implementation of Sockets. Typically used
to implement an Athena server that can be hit by arbitrary TCP clients
(see the file server.sml).

=======================================================================*)

structure Socket = struct

open TextIO
open Posix.Process
open OS.Process

fun readAll(conn) = 
    let val max = 1024 * 80
        fun loop(vector_list,iteration) = 
  	           let val in_vector = Socket.recvVec(conn,max)
	               val len = Word8Vector.length(in_vector)
   	           in
                      if len < max then rev(in_vector::vector_list)
                      else loop(in_vector::vector_list,iteration+1)
                   end
	val vector_list = loop([],1)
     in
        Byte.bytesToString(Word8Vector.concat(vector_list))
     end;

fun makeSingleThreadedServer(input_buffer_size,processRequest) = 
 fn port => 
   let fun run(listener) = let fun accept() = 
                                    let val (conn,conn_addr) = Socket.accept(listener)
	                                val text = readAll(conn)
                                    in
                                       respond(conn,text);                                      
                                       accept()
                                    end
                              and respond(conn,text) = let val reply = processRequest(text)
                                                           val buf = Word8VectorSlice.slice(Byte.stringToBytes reply,0,NONE)
                                                       in
                                                          ignore(Socket.sendVec(conn,buf));
                                                           Socket.close(conn)
                                                       end handle x => (Socket.close(conn);raise x)
                          in 
                             Socket.Ctl.setREUSEADDR(listener,true);
                             Socket.bind(listener,INetSock.any port);
                             Socket.listen(listener,128);
                             accept()
                          end handle x => (Socket.close(listener);raise x)
  in
    run(INetSock.TCP.socket())
  end handle e => (print("\nSomething went wrong" ^ (exnMessage e) ^ "\n");raise e)


fun makeServer(input_buffer_size, processRequest) = 
 fn port => 
   let fun run(listener) = 
           let fun accept() = 
                   let val (conn, conn_addr) = Socket.accept(listener)
                   in
                       case fork() of
                           NONE => (* Child process *)
                               (let val text = readAll(conn)
                                    val reply = processRequest(text)
                                    val buf = Word8VectorSlice.slice(Byte.stringToBytes reply, 0, NONE)
                                in
                                    ignore(Socket.sendVec(conn, buf));
                                    Socket.close(conn);
                                    OS.Process.exit OS.Process.success  (* Exit child process *)
                                end handle x => (Socket.close(conn); OS.Process.exit OS.Process.failure))
                         | SOME _ => (* Parent process *)
                               (Socket.close(conn);  (* Parent closes its copy of the connection *)
                                accept())  (* Continue accepting new connections *)
                   end
               in 
                   Socket.Ctl.setREUSEADDR(listener, true);
                   Socket.bind(listener, INetSock.any port);
                   Socket.listen(listener, 9);
                   accept()
               end handle x => (Socket.close(listener); raise x)
   in
       run(INetSock.TCP.socket())
   end handle e => (print("\nSomething went wrong: " ^ exnMessage e ^ "\n"); raise e)

end

