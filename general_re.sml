(*======================================================================

Regex-related structure used in the implementation of split pattern matching.

=======================================================================*)

structure GeneralRE = 
struct

type 'constraint tag0 = {name: Symbol.symbol option, con: 'constraint option} 

val trivial_tag: 'constraint tag0 = {name = NONE, con = NONE}

datatype ('pat,'constraint) RE0 = 
               lit0 of 'pat * 'constraint tag0 
             | null0 of 'constraint tag0 
             | any0 of 'constraint tag0 
             | backref0 of Symbol.symbol
             | range0 of  real * real * 'constraint tag0
             | concat0 of ('pat,'constraint) RE0 *  ('pat,'constraint) RE0 * 'constraint tag0 
             | union0 of ('pat,'constraint) RE0 * ('pat,'constraint) RE0 * 'constraint tag0 
             | star0 of ('pat,'constraint) RE0 * 'constraint tag0

fun tagOf(lit0(_,t)) = t
  | tagOf(any0(t)) = t
  | tagOf(null0(t)) = t
  | tagOf(concat0(_,_,t)) = t
  | tagOf(range0(_,_,t)) = t
  | tagOf(union0(_,_,t)) = t
  | tagOf(star0(_,t)) = t
  | tagOf(backref0(_)) = trivial_tag 

fun swapTags(lit0(p,t),t') = lit0(p,t')
  | swapTags(any0(t),t') = any0(t')
  | swapTags(null0(t),t') = null0(t')
  | swapTags(concat0(e1,e2,t),t') = concat0(e1,e2,t')
  | swapTags(range0(e1,e2,t),t') = range0(e1,e2,t')
  | swapTags(union0(e1,e2,t),t') = union0(e1,e2,t')
  | swapTags(star0(e,t),t') = star0(e,t')
  | swapTags(e as backref0(_),_) = e

fun reToString(patToString) = 
 (fn (e) => 
    let fun reToString(lit0(pat,t)) = "lit(" ^ (patToString pat) ^ ")"
          | reToString(any0(t)) = "any(" ^ (tagToString t) ^ ")"
          | reToString(null0(t)) = "null(" ^ (tagToString t) ^ ")"
          | reToString(backref0(s)) = "backref(" ^ (Symbol.name(s)) ^ ")"
          | reToString(concat0(e1,e2,t)) = "concat(" ^ (reToString e1) ^ ", " ^ (reToString e2) ^ "," ^ (tagToString t) ^ ")"
          | reToString(range0(e1,e2,t)) = "range(" ^ (Real.toString e1) ^ ", " ^ (Real.toString e2) ^ "," ^ (tagToString t) ^ ")"
          | reToString(union0(e1,e2,t)) = "union(" ^ (reToString e1) ^ ", " ^ (reToString e2) ^ ","  ^ (tagToString t) ^ ")"
          | reToString(star0(e,t)) = "star(" ^ (reToString e) ^ "," ^ (tagToString t) ^ ")"
and tagToString({name=SOME(s),con=NONE}) = "{name=SOME(" ^ (Symbol.name s) ^ "),constraint=NONE}"
  | tagToString({name=SOME(s),con=SOME(_)}) = "{name=SOME(" ^ (Symbol.name s) ^ "),constraint=SOME(_)}"
  | tagToString({name=NONE,con=NONE}) = "{name=NONE,constraint=NONE}"
  | tagToString({name=NONE,con=SOME(_)}) = "{name=NONE,constraint=SOME(_)}"
    in
       reToString(e) 
    end)

end
