structure ModSymbol :> MOD_SYMBOL = 

struct

  structure S = Symbol;

  type mod_symbol = Symbol.symbol list * Symbol.symbol * Symbol.symbol

  fun makeModSymbol x = x 



  fun name(_,_,s) = Symbol.name(s)


  fun nameAsSymbol(_,_,s) = s

  fun modules(syms,_,_) = syms 

  fun modulePrefix0(syms) = (case syms of
                                  [] => ""
                                | _ => (Basic.printListStr(syms,Symbol.name,"."))^".")

  fun modulePrefix(syms,_,_) = modulePrefix0(syms)

  fun makeName(mods,sym) = (modulePrefix0 mods)^(Symbol.name sym)

  fun makeModSymbol'(mods,s) = let val whole = (modulePrefix0 mods)^(S.name s)
                                   val whole_sym = Symbol.symbol whole
                               in
                                 (mods,s,whole_sym)
                               end;

  fun isPlainSymbol(mod_syms,_,_) = null(mod_syms)
   
  fun lastName(_,s,_) = s;

  fun code(_,_,s) = Symbol.code(s)

  fun compare((_,_,s1),(_,_,s2)) = Symbol.compare(s1,s2)

  fun modSymEq((_,_,s1),(_,_,s2)) = Symbol.symEq(s1,s2)

  fun dum_modsym(str) = let val s = Symbol.symbol(str) in makeModSymbol([],s,s) end;


  fun hash(syms,sym,s) = Symbol.hashSymbol(s)

  exception ModSymbol

  val sizeHint =  8543 

  structure H = HashTable

  type 'a htable = (mod_symbol,'a) H.hash_table;
 
  fun makeHTable() = H.mkTable (hash,modSymEq) (sizeHint,ModSymbol)

  fun makeHTableWithInitialSize(size) = H.mkTable (hash,modSymEq) (size,ModSymbol)

  fun clearHTable(ht) = H.clear(ht);

  fun insert(ht,mod_sym,datum) =  H.insert ht (mod_sym,datum);

  fun removeHT(ht,mod_sym) = H.remove ht mod_sym;

  fun insertLst(ht,[]) = ()
    | insertLst(ht,(s,v)::rest) = (insert(ht,s,v);insertLst(ht,rest));
                                    
  fun find(ht,sym) = H.find ht sym;

  fun listItems(ht) = H.listItems ht;

  fun listItemsi(ht) = H.listItemsi ht;

  fun tableToString(ht,f) =
     let fun g(msym,v) = (name msym) ^ " --> " ^ (f v)
	 val L = map g (listItemsi ht)
     in
        Basic.printListStr(L,fn x => x,"\n")
     end

  
  fun exists(ht,sym) = case H.find ht sym of
                          SOME(_) => true
                        | _ => false;

  fun numItems(ht) = H.numItems ht;
  
  fun augmentHT(ht1,ht2) = 
        let val key_val_pairs = listItemsi(ht2)
        in
            List.app (fn (key,v) => insert(ht1,key,v)) key_val_pairs
        end;


  structure Table = IntMapTable(type key = mod_symbol
				fun getInt(_,_,s) = Symbol.code(s))

  type 'a mapping = 'a Table.table

  val removeBinding = Table.remove 

  val empty_mapping = Table.empty

  val enter = Table.enter
  
  fun map(f,m) = Table.map f m 

  fun enterLst(table,[]) = table 
    | enterLst(table,(name,value)::rest) = enterLst(enter(table,name,value),rest);

  val lookUp = Table.look
 
  val listImages = Table.listItems
  val listSymbols = Table.listKeys 

  fun split(syms,sym,_) = (syms,sym)

  val augment = Table.augment

  val mod_sym_comp = (fn ((_,_,s1),(_,_,s2)) => Symbol.compare(s1,s2))


  structure SymSet = MakeSet(type element = mod_symbol val compare = mod_sym_comp);

  type set = SymSet.set;

  val empty_set = SymSet.empty;

  val singleton = SymSet.singleton;

  val isEmpty = SymSet.isEmpty;

  val size = SymSet.size;

  val equal = SymSet.equal;

  val add = SymSet.insert;

  val addLst = SymSet.insertLst;

  val symListToSet = SymSet.listToSet;

  val remove = SymSet.remove; 

  val union = SymSet.union; 

  val setMap = SymSet.map

  val setApp = SymSet.app

  val unionLst = SymSet.unionLst;

  val intersection = SymSet.intersection;

  val difference = SymSet.difference;

  val isMember = SymSet.isMember;

  val listModSymbols = SymSet.listElements;

  val fresh_sym_prefix = "vfs"

  fun restoreTable(msyms,msym_set,msym_ht) = 
       let fun f(msym) = if isMember(msym,msym_set) then () else (removeHT(msym_ht,msym);())
       in
          List.app f msyms
       end handle _ => ()

end
