(*======================================================================

A functor for making set structures, parameterized over elements equipped
with a comparison predicate. 

Copyright (c) 2001-2020 by The Fellowship of SML/NJ
Copyright (c) 1989-2001 by Lucent Technologies

=======================================================================*)

functor MakeSet (type element 
		 val compare: element * element -> General.order) : SET  =

struct

    type element = element 

    abstype set
      = E 
      | T of {
	  elt : element, 
          cnt : int, 
          left : set,
          right : set
	}
with

    fun numItems E = 0
      | numItems (T{cnt,...}) = cnt
        
    val size = numItems

    fun isEmpty E = true
      | isEmpty _ = false

    fun mkT(v,n,l,r) = T{elt=v,cnt=n,left=l,right=r}
      (* N(v,l,r) = T(v,1+numItems(l)+numItems(r),l,r) *)

    fun N(v,E,E) = mkT(v,1,E,E)
      | N(v,E,r as T{cnt=n,...}) = mkT(v,n+1,E,r)
      | N(v,l as T{cnt=n,...}, E) = mkT(v,n+1,l,E)
      | N(v,l as T{cnt=n,...}, r as T{cnt=m,...}) = mkT(v,n+m+1,l,r)

    fun single_L (a,x,T{elt=b,left=y,right=z,...}) = N(b,N(a,x,y),z)
      | single_L _ = raise Match
    fun single_R (b,T{elt=a,left=x,right=y,...},z) = N(a,x,N(b,y,z))
      | single_R _ = raise Match
    fun double_L (a,w,T{elt=c,left=T{elt=b,left=x,right=y,...},right=z,...}) =
          N(b,N(a,w,x),N(c,y,z))
      | double_L _ = raise Match
    fun double_R (c,T{elt=a,left=w,right=T{elt=b,left=x,right=y,...},...},z) =
          N(b,N(a,w,x),N(c,y,z))
      | double_R _ = raise Match

    fun wt (i : int) = i + i + i

    fun T' (v,E,E) = mkT(v,1,E,E)
      | T' (v,E,r as T{left=E,right=E,...}) = mkT(v,2,E,r)
      | T' (v,l as T{left=E,right=E,...},E) = mkT(v,2,l,E)

      | T' (p as (_,E,T{left=T _,right=E,...})) = double_L p
      | T' (p as (_,T{left=E,right=T _,...},E)) = double_R p

        (* these cases almost never happen with small weight*)
      | T' (p as (_,E,T{left=T{cnt=ln,...},right=T{cnt=rn,...},...})) =
            if ln<rn then single_L p else double_L p
      | T' (p as (_,T{left=T{cnt=ln,...},right=T{cnt=rn,...},...},E)) =
            if ln>rn then single_R p else double_R p

      | T' (p as (_,E,T{left=E,...})) = single_L p
      | T' (p as (_,T{right=E,...},E)) = single_R p

      | T' (p as (v,l as T{elt=lv,cnt=ln,left=ll,right=lr},
              r as T{elt=rv,cnt=rn,left=rl,right=rr})) =
          if rn >= wt ln (*right is too big*)
            then
              let val rln = numItems rl
                  val rrn = numItems rr
              in
                if rln < rrn then single_L p else double_L p
              end
          else if ln >= wt rn (*left is too big*)
            then
              let val lln = numItems ll
                  val lrn = numItems lr
              in
                if lrn < lln then single_R p else double_R p
              end
          else mkT(v,ln+rn+1,l,r)

    fun add (E,x) = mkT(x,1,E,E)
      | add (set as T{elt=v,left=l,right=r,cnt},x) = (
          case compare(x,v)
	   of LESS => T'(v,add(l,x),r)
	    | GREATER => T'(v,l,add(r,x))
	    | EQUAL => mkT(x,cnt,l,r)
	  (* end case *))

    fun insert(e,S) = add(S,e)

    fun concat3 (E,v,r) = add(r,v)
      | concat3 (l,v,E) = add(l,v)
      | concat3 (l as T{elt=v1,cnt=n1,left=l1,right=r1}, v, 
                  r as T{elt=v2,cnt=n2,left=l2,right=r2}) =
        if wt n1 < n2 then T'(v2,concat3(l,v,l2),r2)
        else if wt n2 < n1 then T'(v1,l1,concat3(r1,v,r))
        else N(v,l,r)

    fun split_lt (E,x) = E
      | split_lt (T{elt=v,left=l,right=r,...},x) =
          case compare(v,x) of
            GREATER => split_lt(l,x)
          | LESS => concat3(l,v,split_lt(r,x))
          | _ => l

    fun split_gt (E,x) = E
      | split_gt (T{elt=v,left=l,right=r,...},x) =
          case compare(v,x) of
            LESS => split_gt(r,x)
          | GREATER => concat3(split_gt(l,x),v,r)
          | _ => r

    fun min (T{elt=v,left=E,...}) = v
      | min (T{left=l,...}) = min l
      | min _ = raise Match
        
    fun delmin (T{left=E,right=r,...}) = r
      | delmin (T{elt=v,left=l,right=r,...}) = T'(v,delmin l,r)
      | delmin _ = raise Match

    fun delete' (E,r) = r
      | delete' (l,E) = l
      | delete' (l,r) = T'(min r,l,delmin r)

    fun concat (E, s) = s
      | concat (s, E) = s
      | concat (t1 as T{elt=v1,cnt=n1,left=l1,right=r1}, 
                  t2 as T{elt=v2,cnt=n2,left=l2,right=r2}) =
          if wt n1 < n2 then T'(v2,concat(t1,l2),r2)
          else if wt n2 < n1 then T'(v1,l1,concat(r1,t2))
          else T'(min t2,t1, delmin t2)


    local
      fun trim (lo,hi,E) = E
        | trim (lo,hi,s as T{elt=v,left=l,right=r,...}) =
            if (compare(v,lo) = General.GREATER)
              then if (compare(v,hi) = General.LESS) then s else trim(lo,hi,l)
              else trim(lo,hi,r)
                
      fun uni_bd (s,E,_,_) = s
        | uni_bd (E,T{elt=v,left=l,right=r,...},lo,hi) = 
             concat3(split_gt(l,lo),v,split_lt(r,hi))
        | uni_bd (T{elt=v,left=l1,right=r1,...}, 
                   s2 as T{elt=v2,left=l2,right=r2,...},lo,hi) =
            concat3(uni_bd(l1,trim(lo,v,s2),lo,v),
                v, 
                uni_bd(r1,trim(v,hi,s2),v,hi))
              (* inv:  lo < v < hi *)

        (* all the other versions of uni and trim are
         * specializations of the above two functions with
         *     lo=-infinity and/or hi=+infinity 
         *)

      fun trim_lo (_, E) = E
        | trim_lo (lo,s as T{elt=v,right=r,...}) =
            case compare(v,lo) of
              GREATER => s
            | _ => trim_lo(lo,r)

      fun trim_hi (_, E) = E
        | trim_hi (hi,s as T{elt=v,left=l,...}) =
            case compare(v,hi) of
              LESS => s
            | _ => trim_hi(hi,l)
                
      fun uni_hi (s,E,_) = s
        | uni_hi (E,T{elt=v,left=l,right=r,...},hi) = 
             concat3(l,v,split_lt(r,hi))
        | uni_hi (T{elt=v,left=l1,right=r1,...}, 
                   s2 as T{elt=v2,left=l2,right=r2,...},hi) =
            concat3(uni_hi(l1,trim_hi(v,s2),v),v,uni_bd(r1,trim(v,hi,s2),v,hi))

      fun uni_lo (s,E,_) = s
        | uni_lo (E,T{elt=v,left=l,right=r,...},lo) = 
             concat3(split_gt(l,lo),v,r)
        | uni_lo (T{elt=v,left=l1,right=r1,...}, 
                   s2 as T{elt=v2,left=l2,right=r2,...},lo) =
            concat3(uni_bd(l1,trim(lo,v,s2),lo,v),v,uni_lo(r1,trim_lo(v,s2),v))

      fun uni (s,E) = s
        | uni (E,s) = s
        | uni (T{elt=v,left=l1,right=r1,...}, 
                s2 as T{elt=v2,left=l2,right=r2,...}) =
            concat3(uni_hi(l1,trim_hi(v,s2),v), v, uni_lo(r1,trim_lo(v,s2),v))

    in
      val hedge_union = uni
    end

    fun old_union (E,s2)  = s2
      | old_union (s1,E)  = s1
      | old_union (T{elt=v,left=l,right=r,...},s2) = 
          let val l2 = split_lt(s2,v)
              val r2 = split_gt(s2,v)
          in
            concat3(old_union(l,l2),v,old_union(r,r2))
          end

    val empty = E

    fun singleton x = T{elt=x,cnt=1,left=E,right=E}

    fun addList (s,l) = List.foldl (fn (i,s) => add(s,i)) s l

    fun insertLst(elst,S) = addList(S,elst)

    fun listToSet(elem_list) = addList(empty,elem_list)
 
    val add = add

    fun member (set, x) = let
	  fun pk E = false
	    | pk (T{elt=v, left=l, right=r, ...}) = (
		case compare(x,v)
		 of LESS => pk l
		  | EQUAL => true
		  | GREATER => pk r
		(* end case *))
	  in
	    pk set
	  end

    fun isMember(a,S) = member(S,a)


    local
        (* true if every item in t is in t' *)
      fun treeIn (t,t') = let
            fun isIn E = true
              | isIn (T{elt,left=E,right=E,...}) = member(t',elt)
              | isIn (T{elt,left,right=E,...}) = 
                  member(t',elt) andalso isIn left
              | isIn (T{elt,left=E,right,...}) = 
                  member(t',elt) andalso isIn right
              | isIn (T{elt,left,right,...}) = 
                  member(t',elt) andalso isIn left andalso isIn right
            in
              isIn t
            end
    in
    fun isSubset (E,_) = true
      | isSubset (_,E) = false
      | isSubset (t as T{cnt=n,...},t' as T{cnt=n',...}) =
          (n<=n') andalso treeIn (t,t')

    fun equal (E,E) = true
      | equal (t as T{cnt=n,...},t' as T{cnt=n',...}) =
          (n=n') andalso treeIn (t,t')
      | equal _ = false
    end

    local
      fun next ((t as T{right, ...})::rest) = (t, left(right, rest))
	| next _ = (E, [])
      and left (E, rest) = rest
	| left (t as T{left=l, ...}, rest) = left(l, t::rest)
    in
    fun comp (s1, s2) = let
	  fun cmp (t1, t2) = (case (next t1, next t2)
		 of ((E, _), (E, _)) => EQUAL
		  | ((E, _), _) => LESS
		  | (_, (E, _)) => GREATER
		  | ((T{elt=e1, ...}, r1), (T{elt=e2, ...}, r2)) => (
		      case compare(e1, e2)
		       of EQUAL => cmp (r1, r2)
			| order => order
		      (* end case *))
		(* end case *))
	  in
	    cmp (left(s1, []), left(s2, []))
	  end
    end

    fun delete (E,x) = raise LibBase.NotFound
      | delete (set as T{elt=v,left=l,right=r,...},x) =
          case compare(x,v) of
            LESS => T'(v,delete(l,x),r)
          | GREATER => T'(v,l,delete(r,x))
          | _ => delete'(l,r)

    fun remove(a,S) = delete(S,a) handle LibBase.NotFound => S

    val union = hedge_union

    fun unionLst(set_list) = 
          let fun f([],res) = res
                | f(s::more,res) = f(more,union(s,res))
          in
             f(set_list,empty)
          end;

    fun intersection (E, _) = E
      | intersection (_, E) = E
      | intersection (s, T{elt=v,left=l,right=r,...}) = let
	  val l2 = split_lt(s,v)
	  val r2 = split_gt(s,v)
          in
            if member(s,v)
	      then concat3(intersection(l2,l),v,intersection(r2,r))
	      else concat(intersection(l2,l),intersection(r2,r))
          end

    fun difference (E,s) = E
      | difference (s,E)  = s
      | difference (s, T{elt=v,left=l,right=r,...}) =
          let val l2 = split_lt(s,v)
              val r2 = split_gt(s,v)
          in
            concat(difference(l2,l),difference(r2,r))
          end

    fun map f set = let
	  fun map'(acc, E) = acc
	    | map'(acc, T{elt,left,right,...}) =
		map' (add (map' (acc, left), f elt), right)
	  in 
	    map' (E, set)
	  end

    fun app apf =
         let fun apply E = ()
               | apply (T{elt,left,right,...}) = 
                   (apply left;apf elt; apply right)
         in
           apply
         end

    fun foldl f b set = let
	  fun foldf (E, b) = b
	    | foldf (T{elt,left,right,...}, b) = 
		foldf (right, f(elt, foldf (left, b)))
          in
            foldf (set, b)
          end

    fun foldr f b set = let
	  fun foldf (E, b) = b
	    | foldf (T{elt,left,right,...}, b) = 
		foldf (left, f(elt, foldf (right, b)))
          in
            foldf (set, b)
          end

    fun listItems set = foldr (op::) [] set

    val listElements = listItems

    fun filter pred set =
	  foldl (fn (item, s) => if (pred item) then add(s, item) else s)
	    empty set

    fun find p E = NONE
      | find p (T{elt,left,right,...}) = (case find p left
	   of NONE => if (p elt)
		then SOME elt
		else find p right
	    | a => a
	  (* end case *))

    fun exists p E = false
      | exists p (T{elt, left, right,...}) =
	  (exists p left) orelse (p elt) orelse (exists p right)

end

end
