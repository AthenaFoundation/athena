structure Symbol :> SYMBOL = 

struct

  type symbol = string * int
       
  structure H = HashTable

  exception Symbol

  val nextsym = ref 0

(** The following initial hash table size seems to work well in practice: **)

  val sizeHint = 7561

  fun hashSymbol(s,i) = Basic.hashInt(i)

  val hashtable : (string,int) H.hash_table = 
          		H.mkTable(HashString.hashString, op = ) (sizeHint,Symbol)

  val fresh_fun_sym_prefix = ref "f"

  val fresh_counter = ref 0

  fun freshSymbol(str_opt) = 
       let val index = (fresh_counter := !fresh_counter + 1;Int.toString(!fresh_counter))
           val name_try = (case str_opt of 
                              SOME(str) => str^index
                            | _ => (!fresh_fun_sym_prefix)^index)
       in
         (case H.find hashtable name_try of
             SOME(code) => freshSymbol(str_opt)
           | _ => let val i = !nextsym
                      val _ = nextsym := i + 1
                      val sym = (name_try,i)
                      val _ = H.insert hashtable sym
                  in sym end)
       end;

  fun printSymCounter() = print("\nNext symbol code: " ^ (Int.toString(!nextsym)) ^ "\n");

  fun symbol name =
    let val res = case H.find hashtable name
                     of SOME i => (name,i)
                      | NONE => let val i = !nextsym
   	                        in 
                                   nextsym := i+1;
		                   H.insert hashtable (name,i);
		                   (name,i)
		                end
    in
      res 
    end 

  fun makePrivateString(s) = ")"^s;
  fun makePrivateSymbol(s) = symbol(makePrivateString(s));

  fun str_2_sym name = symbol name

  fun name(s,n) = s

  fun code(s,n) = n

  fun compare((_,n1),(_,n2)) = Int.compare(n1,n2);

  fun symEq((s1,n1),(s2,n2)) = (n1 = n2)

  type 'a htable = ((string * int),'a) H.hash_table;

  fun makeHTable() = 
       let fun hashFunction(s:string,i:int) = Basic.hashInt(i)
           in
               H.mkTable (hashFunction,symEq) (sizeHint,Symbol)
       end;

  fun makeHTableWithInitialSize(size) = 
       let fun hashFunction(s:string,i:int) = HashString.hashString(s)
           in
               H.mkTable (hashFunction,symEq) (size,Symbol)
       end;

  fun clearHTable(ht) = H.clear(ht);

  fun insert(ht,sym,datum) =  H.insert ht (sym,datum);

  fun removeHT(ht,sym) = H.remove ht sym;

  fun insertLst(ht,[]) = ()
    | insertLst(ht,(s,v)::rest) = (insert(ht,s,v);insertLst(ht,rest));
                                    
  fun find(ht,sym) = H.find ht sym;

  fun exists(ht,sym) = case H.find ht sym of
                          SOME(_) => true
                        | _ => false;

  fun numItems(ht) = H.numItems ht;

  fun listItems(ht) = H.listItems ht;

  fun listItemsi(ht) = H.listItemsi ht;

  fun augmentHT(ht1,ht2) = 
        let val key_val_pairs = listItemsi(ht2)
        in
            List.app (fn (key,v) => insert(ht1,key,v)) key_val_pairs
        end;  


  structure Table = IntMapTable(type key = symbol
				fun getInt(_,n) = n)


  type 'a mapping = 'a Table.table

  val removeBinding = Table.remove 

  val empty_mapping = Table.empty

  fun make_empty_mapping() = empty_mapping

  val enter = Table.enter
  
  fun map(f,m) = Table.map f m 

  fun enterLst(table,[]) = table 
    | enterLst(table,(name,value)::rest) = enterLst(enter(table,name,value),rest);

  val lookUp = Table.look

  val listImages = Table.listItems;

  fun listSymbolsInDomain(m) = 
        let val all_symbols = List.map (fn (s,_) => symbol(s)) (H.listItemsi hashtable)
        in 
           List.filter (fn s => case Table.look(m,s) of SOME(_) => true | _ => false) all_symbols
        end;

  fun listSymbolsAndImages(m) =
        let val all_symbols = List.map (fn (s,_) => symbol(s)) (H.listItemsi hashtable)
            fun loop([],res) = res
              | loop(s::more,res) = (case Table.look(m,s) of 
                                        SOME(x) => loop(more,(s,x)::res)
                                      | _ => loop(more,res))
        in 
           loop(all_symbols,[])
        end;         

  fun domainSize(m) = Table.domainSize(m);

  val augment = Table.augment

  structure SymbolKey : ORD_KEY = 
  struct
	type ord_key = symbol
        val compare = compare
  end;

  structure SymbolTable: ORDERED_MAP = makeOrdMap(SymbolKey)

  type 'a mappingWD = (symbol * 'a) Table.table

  fun removeBindingWD(m,sym) = let val (m',(_,v)) = Table.remove(m,sym)
                               in
                                  (m',v)
                               end

  val empty_mappingWD = Table.empty

  fun enterWD(m,sym,v) = Table.enter(m,sym,(sym,v))

  fun enterLstWD(table,[]) = table 
    | enterLstWD(table,(name,value)::rest) = enterLstWD(enterWD(table,name,value),rest);

  fun augmentWD(m1,m2) = 
         let val L = Table.listItems m2
             fun f(m,[]) = m
               | f(m,(sym,v)::rest) = 
                     (case Table.look(m2,sym) of
                         SOME((_,v')) => f(Table.enter(m,sym,(sym,v')),rest))
         in
            f(m1,L)
         end 

  fun lookUpWD(m:'a mappingWD,s:symbol) = 
          (case Table.look(m,s) of
               SOME((_,v)) => SOME v
            | _ => NONE)

  fun mapWD(f:'a -> 'a,m:'a mappingWD) = Table.map (fn (s,v) => (s,f v))  m
  

  fun listImagesWD(m:'a mappingWD) = 
     (List.map (fn (_,v) => v) (Table.listItems m)) 

  fun listSymbolsAndImagesWD(m:'a mappingWD) = Table.listItems m 

  fun listSymbolsInDomainWD(m:'a mappingWD) = (List.map (fn (s,_) => s) (Table.listItems m))
 
  val domainSizeWD = Table.domainSize

  val listMapSymbols = Table.listKeys  

  val sym_comp = (fn ((_,n1),(_,n2)) => (Int.compare(n1,n2)));

  structure SymSet = MakeSet(type element = symbol val compare = sym_comp);

  type set = SymSet.set;

  val empty_set = SymSet.empty;

  val setMap = SymSet.map
  val setApp = SymSet.app

  val singleton = SymSet.singleton;

  val isEmpty = SymSet.isEmpty;

  val size = SymSet.size;

  val equal = SymSet.equal;

  val add = SymSet.insert;

  val addLst = SymSet.insertLst;

  val symListToSet = SymSet.listToSet;

  val remove = SymSet.remove; 

  val union = SymSet.union; 

  val unionLst = SymSet.unionLst;

  val intersection = SymSet.intersection;

  val difference = SymSet.difference;

  val isMember = SymSet.isMember;

  val listSymbols = SymSet.listElements;

  val fresh_sym_prefix = "vfs"

  fun fresh(syms) = let val index = ref 0
                        fun inc() = (Basic.inc(index);!index)
			fun findIndex() = 
				let val s = symbol(fresh_sym_prefix^(Int.toString(inc())))
				in
				   if isMember(s,syms) then findIndex() else s
				end
		    in findIndex () end;
					  
end
