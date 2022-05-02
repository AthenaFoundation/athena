(*======================================================================

This is the implementation type of Athena meta-identifiers (terms of sort Ide).

=======================================================================*)

signature META_ID =sig

  eqtype meta_id
  exception MetaId

  val makeMetaId : string -> meta_id
  val name : meta_id -> string
  val code: meta_id -> int 
  val eq: meta_id * meta_id -> bool
  val hash: meta_id -> Word.word 
  val compare: meta_id * meta_id -> order

end;
