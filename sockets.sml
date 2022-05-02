(*======================================================================

This is a self-contained SML implementation of Sockets. Typically used
to implement an Athena server that can be hit by arbitrary TCP clients
(see the file server.sml).

=======================================================================*)

structure Socket = struct

open TextIO

fun padMessageToServer(msg) = 
     let val len = String.size(msg)
         val init_zero_count = 20 - len
         val init_zero_segment = implode(map (fn _ => #"0") (Basic.fromI2N(1,init_zero_count)))
     in
        String.concat([init_zero_segment,msg])
     end

fun chopPrefix(V,n) = 
    let val len = Word8Vector.length(V)
        val len' = len - n
	val L = List.tabulate(len',fn i => Word8Vector.sub(V,i+n))
    in
       Word8Vector.fromList(L)
    end

fun getPayloadSize(V) = 
     let val first_20 = Byte.bytesToString(Word8Vector.fromList(List.tabulate(20,fn i => Word8Vector.sub(V,i))))
     in
       (case Int.fromString(first_20) of
           SOME(i) => i + 20
         | _ => 20)
     end

fun readAll(conn) = 
    let val payload_size = ref(1)
        fun loop(vector_list,bytes_read_last_time,total_bytes_read_so_far,iteration) = 
             if ((total_bytes_read_so_far < !payload_size) andalso (bytes_read_last_time > 0)) then
  	           let val in_vector = Socket.recvVec(conn,200000)
	               val len = Word8Vector.length(in_vector)
		       val _ = print("\nIteration #"^(Int.toString(iteration))^
                                     ", just read a chunk of length " ^ (Int.toString(len)))
		       val in_vector' = if iteration < 2 then 
                                           (payload_size := getPayloadSize(in_vector);
					    print("\nPAYLOAD SIZE: " ^ (Int.toString(!payload_size)) ^ "\n");
                                            chopPrefix(in_vector,20))
                                        else in_vector
   	           in
                      loop(in_vector'::vector_list,len,len + total_bytes_read_so_far,iteration+1)
                   end
             else rev(vector_list)
	val vector_list = loop([],1,0,1)
     in
        Byte.bytesToString(Word8Vector.concat(vector_list))
     end;

fun makeServer(input_buffer_size,processRequest) = 
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
                             Socket.listen(listener,9);
                             accept()
                          end handle x => (Socket.close(listener);raise x)
  in
    run(INetSock.TCP.socket())
  end handle x => (print("\nSomething went wrong...\n");raise x)

end

