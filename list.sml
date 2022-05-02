functor MakeList (type element): LIST =

struct

type element = element

datatype node = null | Node of {data:element,next: node ref}

fun makeNode(x) = Node({data=x,next=ref(null)});

val limit = ref(1024)

fun setCapacity(c) = limit := c

type drop_list = {front:node ref, back: node ref,first_chunk:node list ref,first_chunk_filled:bool ref}

fun firstPartFilled({first_chunk_filled,...}:drop_list) = !first_chunk_filled

fun firstPart({first_chunk,...}:drop_list) = map (fn Node({data,...}) => data) (!first_chunk)

fun assign(l1:drop_list,l2:drop_list) = 
      (#front(l1) := !(#front(l2));
       #back(l1) :=  !(#back(l2));
       #first_chunk(l1) := !(#first_chunk(l2));
       #first_chunk_filled(l1) := !(#first_chunk_filled(l2)));

fun toList(L:drop_list as {back,first_chunk,...},{with_first_part}) = 
       let fun loop(null,res) = res
             | loop(Node({data,next}),res) = loop(!next,data::res)
           val main_res = loop(!back,[])
       in
        if with_first_part then 
           main_res @ (map (fn Node({data,...}) => data) (!first_chunk))
        else main_res 
       end;

fun map(f,L,{with_first_part=wfp}) = List.map f (toList(L,{with_first_part=wfp}))
  
fun makeList(x,N) = 
 let val (f,b) = (ref(null),ref(null))
     fun loop(i,most_recent as Node({next,...})) = 
           if i > N then 
              f := most_recent
           else let val new_node = makeNode(x)
                    val _ = next := new_node
                in
                   loop(i+1,new_node)
                end
     val first_node = makeNode(x)
     val _ = b := first_node
     val _ = loop(2,first_node)
  in
    {front=f,back=b,first_chunk=ref([]),first_chunk_filled=ref(false)}
  end;

fun prepend(x,list as {front,back,first_chunk,first_chunk_filled}) = 
     if !first_chunk_filled then 
        let val new_node = makeNode(x)
            val Node({next=fnext,...}) = !front
            val Node({next=bnext,...}) = !back
            val _ = fnext := new_node
            val _ = front := new_node
         in
           back := !bnext
         end
     else
        let val new_node = makeNode(x)
            val _ = first_chunk := new_node::(!first_chunk)
         in
            if length(!first_chunk) >= !limit then
               first_chunk_filled := true
            else ()
         end

fun listLength(L) = List.length(map(fn x => x,L,{with_first_part=true}))

end

