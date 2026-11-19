(*======================================================================

Implementation of the Athena term variable API specified in ath-term-var.sig.

=======================================================================*)

structure AthTermVar : ATH_TERM_VAR =

struct

  structure F = FTerm

  type sort = F.term


(**
    An Athena term variable is just an atom (as implemented by the SML Atom signature, which provides hashed strings
    with fast equality testing) along with a sort, where a sort is a 'fast term' (implemented in fterm.sml).
**)

  type ath_term_var = (Atom.atom * sort)

  fun getSort(_,s) = s

  fun hash((a,_)) = Atom.hash(a)

  fun swapSorts((a,_),new_sort) = (a,new_sort)

  fun applySortSub(sub,(a,s)) = (a,F.applySub(sub,s))

  fun renameSortVars((a,sort),sub) = 
      let val (sort',sub') = FTerm.renameAux(sort,sub)	      
      in
        ((a,sort'),sub')
      end

  fun applySortSubLst(sub,vars) = map (fn (v) =>  applySortSub(sub,v)) vars

  fun isPoly(_,s) = not(F.isGround(s))

  fun compareNames((a1,_),(a2,_)) = Atom.compare(a1,a2)

  fun tagVar(a,s) = (a,F.tagSort(s))

  fun isTagged(a,s) = F.someTaggedVars(s)
         
  fun athTermVarEq((a1,s1),(a2,s2)) = Atom.sameAtom(a1,a2) andalso F.sortEq(s1,s2)
    
  fun athTermVarLitEq((a1,s1),(a2,s2)) = Atom.sameAtom(a1,a2) andalso F.termEq(s1,s2)
          
  fun nameEq((a1,_),(a2,_)) = Atom.sameAtom(a1,a2)

  exception Atom_Table

  structure H = HashTable

  val sizeHint = 3571
         
  val name_table : (Atom.atom,bool) H.hash_table = 
       let fun  hashFunction(a:Atom.atom) = Atom.hash(a)
       in
          H.mkTable(hashFunction,Atom.sameAtom) (sizeHint,Atom_Table)
       end

(*======================= Hash Tables For Athena Variables =======================*)

  exception Ath_Term_Var

  type 'a htable = (ath_term_var,'a) H.hash_table

  fun makeHTable() = 
       let fun hashFunction(a:Atom.atom,sort:F.term) = Atom.hash(a)
           in
               H.mkTable (hashFunction,athTermVarEq) (sizeHint,Ath_Term_Var)
           end

  fun makeHTableWithVarEq(varEqFun) = 
       let fun hashFunction(a:Atom.atom,sort:F.term) = Atom.hash(a)
           in
               H.mkTable (hashFunction,varEqFun) (sizeHint,Ath_Term_Var)
           end

  fun insert(ht,atv,datum) =  H.insert ht (atv,datum)

  fun clearTable(ht) = H.clear(ht)

  fun removeHT(ht,atv) =  H.remove ht atv

  fun find(ht,atv) = H.find ht atv

  fun exists(ht,atv) = case H.find ht atv of
                          SOME(_) => true
                        | _ => false

  fun numItems(ht) = H.numItems ht

  fun listItems(ht) = H.listItems ht

  fun listItemsi(ht) = H.listItemsi ht

fun athTermVarWithSort(name,sort) = 
      let val name_atom = Atom.atom(name)
      in 
        (case H.find name_table name_atom
            of SOME (_) => (name_atom,sort)
             | NONE => let val _ = H.insert name_table (name_atom,true)
                       in          
                         (name_atom,sort)
 		       end)
      end

fun athTermVar name = athTermVarWithSort(name,F.makeFreshVar())

val fresh_counter:InfNum.inf_num ref = ref (InfNum.makeInfNum())

fun name(a,_) = Atom.toString(a)


fun compare((a1,s1),(a2,s2)) = 
      let val r = Atom.compare(a1,a2)
      in
	if r = EQUAL then (if F.variants(s1,s2) then EQUAL else F.compare(s1,s2))
	else r
      end

val fresh_name_prefix = Names.fresh_var_name_prefix

fun freshVarAtom(str_opt) = let val index = InfNum.toString(!fresh_counter)
                                val _ = fresh_counter := InfNum.increment(!fresh_counter)
                                val name_try = (case str_opt of 
                                                   SOME(str) => str^index
                                                 | _ => ((Names.fresh_var_name_prefix)^index))
                                val name_try_atom = Atom.atom(name_try)
		            in
                              (case H.find name_table name_try_atom of
                                  SOME _ => freshVarAtom(str_opt)
                                | _ => let val _ = H.insert name_table (name_try_atom,true)
                                       in
                                          name_try_atom
                                       end)
                            end

fun freshVarName() = Atom.toString(freshVarAtom(NONE))

fun fresh() = (freshVarAtom(NONE),F.makeFreshVar())

fun freshWithPrefix(str) = (freshVarAtom(SOME(str)),F.makeFreshVar())

fun freshLst(L) = map (fn (_) => fresh()) L

fun freshWithSort(sort) = (freshVarAtom(NONE),sort)

fun freshWithSortAndPrefix(str,sort) = (freshVarAtom(SOME(str)),sort)

fun changeNames((_,sort),name) =  athTermVarWithSort(name,sort)

fun toStringWithSort((a,sort)) = (Atom.toString a)^":"^(F.toStringDefault sort)

val toStringDefault = toStringWithSort

  fun toString((a,s),printVarSort) = 
	 (Names.variable_prefix)^(Atom.toString(a))^
	  (if (!(Options.print_var_sorts)) then ":"^(F.toString(s,printVarSort)) else "")

  fun toPrettyString(s,(a,sort),printVarSort) = 
                            (Names.variable_prefix)^(Atom.toString(a))^(if (!(Options.print_var_sorts)) 
			    then ":"^(F.toPrettyString(s+(String.size(Atom.toString(a)))+2,
				      sort,printVarSort)) else "")

  fun toPrettyStringDefault(s,v) = toPrettyString(s,v,F.varToString)

  fun toPrettyStringDefaultLst(s,vars) = map (fn v => toPrettyString(s,v,F.varToString)) vars 

  fun varListsMatch(vars1,vars2) = 
     let val (sorts1,sorts2) = (map getSort vars1,map getSort vars2)
     in
       (case (F.matchLst(sorts1,sorts2),F.matchLst(sorts2,sorts1)) of
           (SOME(_),SOME(_)) => true
         | _ => false)
     end

  fun varInstance(v1 as (a1,s1),v2 as (a2,s2)) = Atom.sameAtom(a1,a2) andalso F.matches(s1,s2)


fun toJson(v) = JSON.OBJECT([("type", JSON.STRING("term")),
	  	 	     ("subtype", JSON.STRING("variable")),
	  	 	     ("root", JSON.STRING(toStringDefault(v))),
	  	 	     ("children", JSON.ARRAY([]))])

  structure ATVKey : ORD_KEY = 
  struct
	type ord_key = ath_term_var
        val compare = compare
  end

  structure ATVNameKey : ORD_KEY = 
  struct
	type ord_key = ath_term_var
        val compare = compareNames
  end

  structure Table: ORDERED_MAP = makeOrdMap(ATVKey)
  structure NameOnlyTable: ORDERED_MAP = makeOrdMap(ATVNameKey)

  type 'a mapping = 'a Table.map

  val empty_mapping = Table.empty

  val isEmptyMapping = Table.isEmpty

  fun enter(t:'a mapping,v:ath_term_var,x: 'a) = Table.insert(t,v,x)

  val listImages = Table.listItems

  val listAll = Table.listItemsi

  val foldl  = Table.foldl

  val map = Table.map 

  fun enter_lst(table,[]) = table 
    | enter_lst(table,(v,x)::rest) = enter_lst(enter(table,v,x),rest)

  val lookUp = Table.find

  fun augment(t1,t2,[]) = t1 
    | augment(t1,t2,v::rest) = (case Table.find(t2,v) of
                                        NONE => augment(t1,t2,rest)
                                      | SOME(x) => augment(enter(t1,v,x),t2,rest))


  type 'a name_mapping = 'a NameOnlyTable.map

  val isEmptyNameMapping = NameOnlyTable.isEmpty 
 
  val empty_name_mapping = NameOnlyTable.empty

  fun nameEnter(t:'a name_mapping,v:ath_term_var,x: 'a) = NameOnlyTable.insert(t,v,x)

  val nameListImages = NameOnlyTable.listItems

  val nameListAll = NameOnlyTable.listItemsi

  val nameFoldl  = NameOnlyTable.foldl

  val nameMap = NameOnlyTable.map 

  fun nameEnterLst(table,[]) = table 
    | nameEnterLst(table,(v,x)::rest) =  nameEnterLst(nameEnter(table,v,x),rest)

  val nameLookUp = NameOnlyTable.find

  fun nameAugment(t1,t2,[]) = t1 
    | nameAugment(t1,t2,v::rest) = (case NameOnlyTable.find(t2,v) of
                                        NONE => nameAugment(t1,t2,rest)
                                      | SOME(x) => nameAugment(nameEnter(t1,v,x),t2,rest))


  structure VSet = MakeSet(type element = ath_term_var
                           val compare = compare)

  type var_set = VSet.set

  val empty = VSet.empty

  val isEmpty = VSet.isEmpty

  val size = VSet.size

  val equal = VSet.equal

  val isSubset = VSet.isSubset

  val add = VSet.insert

  val addLst = VSet.insertLst

  val remove = VSet.remove

  val listVars = VSet.listElements

  val union = VSet.union

  val intersection = VSet.intersection

  val isMember = VSet.isMember

  fun simpleMerge(vars1,vars2) = 
    let fun f([],L) = L
          | f(L,[]) = L
          | f(L1 as v1::L1',L2 as v2::L2') = 
		let val r = compareNames(v1,v2)	     
		in
		    if r = EQUAL then v1::f(L1',L2')
  	            else (if r = LESS then v1::f(L1',L2) else v2::f(L1,L2'))
		end
    in
	f(vars1,vars2)
    end 

  fun update(vars,true_vars) =
	let fun f([],L) = []
              | f(L,[]) = L 
              | f(L1 as v1::rest1, L2 as v2::rest2) = 
		let val r = compareNames(v1,v2)	     
		in
		    if r = EQUAL then v2::f(rest1,rest2)
  	            else (if r = GREATER then f(L1,rest2) else raise Basic.Never)
		end
      	in
	   f(vars,true_vars)
	end

  fun updatePolyConstants(poly_constants_and_sorts,poly_constants_and_sorts') = 
	let fun f([],L) = []
              | f(L,[]) = L 
              | f(L1 as (c1,sort1)::rest1, L2 as (c2,sort2)::rest2) = 
		let val r = ModSymbol.compare(c1,c2)	     
		in
		    if r = EQUAL then (c2,sort2)::(f(rest1,rest2))
  	            else (if r = GREATER then f(L1,rest2) else raise Basic.Never)
		end
      	in
	   f(poly_constants_and_sorts,poly_constants_and_sorts')
	end		

  fun simpleMergeLst(objects: 'a list, getVars: 'a -> ath_term_var list) = 
    let fun f([],res) = res
          | f(x::more,res) = f(more,simpleMerge(getVars x,res))
    in
       f(objects,[])
    end

fun reconcilePolyConstants(objects, getConstantsAndTheirSorts, in_theta) = 
 		 let val glb_disagreements = ref(false)
		     fun g(L1,L2,theta) = 
		          let val sub = ref(theta)
			      fun f([],L2) = L2
 	 		        | f(L1,[]) = L1 
			        | f(L1 as (c1,s1)::L1',L2 as (c2,s2)::L2') = 
				     let val r = ModSymbol.compare(c1,c2)
					 val  (sort1,sort2) = (F.applySub(!sub,s1),
							       F.applySub(!sub,s2))
				     in
			   	       if r = EQUAL andalso F.variants(sort1,sort2) then 
					(let val ground_sorts = F.areAllGround([sort1,sort2])
					 in
					    if F.hasOrderSortedDomains(sort1) orelse F.hasOrderSortedDomains(sort2)
					    then 
					      let val common_sort = F.makeFreshVar() 
						  val (theta,disagreements) = F.getGlbModuloVarSort(common_sort,sort1,sort2)
						  val _ = glb_disagreements := (!glb_disagreements orelse 
										 disagreements)
						  val _ = if ground_sorts then () 
						          else sub := F.composeSubs(theta,!sub)
						  val sort1' = if ground_sorts then F.applySub(theta,common_sort)
							       else common_sort 
					      in 
						 (c1,sort1')::(f(L1',L2'))
					      end
					   else  
					      let val theta = F.empty_sub (* F.unifyEx(sort1,sort2) *)
						  val _ =  sub := F.composeSubs(theta,!sub)
						  val sort1' = F.applySub(theta,sort1)
					      in
						 (c1,sort1')::(f(L1',L2'))
					      end
					 end)
				       else (if r = LESS then (c1,sort1)::(f(L1',L2))
					      else (c2,sort2)::(f(L1,L2')))
				     end
                         in
			    (f(L1,L2),!sub)
			 end
		     fun loop([],res) = (res,!glb_disagreements)
		       | loop(t::more,(L,theta)) = loop(more,g(getConstantsAndTheirSorts(t),L,theta))

		 in
		   loop(objects,([],in_theta))
		 end

(*** Caution: Everytime reconcileVars is applied to obtain a result of the form  *****)
(*** ((new_vars,theta),vars_diff), ensure that theta is applied to new_vars      *****)
(*** to obtain a new list new_vars' that reflects all the constraints discovered *****)
(*** by theta. 									 *****)

  fun reconcileVars(objects: 'a list, getVars: 'a -> ath_term_var list,in_theta) = 
 		 let val glb_disagreements = ref(false)
		     fun g(L1,L2,theta) = 
		          let val sub = ref(theta)
			      fun f([],L2) = L2
 	 		        | f(L1,[]) = L1 
			        | f(L1 as v1::L1',L2 as v2::L2') = 
				     let val r = compareNames(v1,v2)
					 val  (sort1,sort2) = (F.applySub(!sub,getSort(v1)),
							       F.applySub(!sub,getSort(v2)))
				     in
			   	       if r = EQUAL then
					(let val (is_ground_1,is_ground_2) = (F.isGround(sort1),F.isGround(sort2))
                                             val ground_sorts = is_ground_1 andalso is_ground_2 
					 in
					    if F.hasOrderSortedDomains(sort1) orelse F.hasOrderSortedDomains(sort2)
					    then 
					      let val common_sort = F.makeFreshVar() 
						  val (theta,disagreements) = F.getGlbWithGroundInfo(common_sort,sort1,sort2,is_ground_1,is_ground_2,ground_sorts)
						  val _ = glb_disagreements := (!glb_disagreements orelse 
										 disagreements)
						  val _ = if ground_sorts then () 
						          else sub := F.composeSubs(theta,!sub)
						  val sort1' = if ground_sorts then F.applySub(theta,common_sort)
							       else common_sort 
					      in 
						 (swapSorts(v1,sort1'))::f(L1',L2')
					      end
					   else  
					      let val theta = F.unifyEx(sort1,sort2) 
					          (* unifyEx might fail; this should be handled by clients. *)
 						  val _ =  sub := F.composeSubs(theta,!sub)
						  val sort1' = F.applySub(theta,sort1)
					      in
						 (swapSorts(v1,sort1'))::f(L1',L2')
					      end
					 end)
				       else (if r = LESS then (swapSorts(v1,sort1))::f(L1',L2) 
					      else (swapSorts(v2,sort2))::f(L1,L2'))
				     end
                         in
			    (f(L1,L2),!sub)
			 end
		     fun loop([],res) = (res,!glb_disagreements)
		       | loop(t::more,(L,theta)) = loop(more,g(getVars(t),L,theta))

		 in
		   loop(objects,([],in_theta))
		 end

end (* end of the AthTermVar structure *)
