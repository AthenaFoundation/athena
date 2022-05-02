(*
Code by Neophytos Michael, implementing the Mersenni Twister
algorithm of Makoto Matsumoto and Takuji Nishimura
*)

structure MT : MT =
struct
  structure A = Array 
  structure R = Real

  type state = Word32.word array * int ref
  type rand = unit -> Word32.word
  val op^ = Word32.xorb
  val <<  = Word32.<<
  val >>  = Word32.>>
  val ||  = Word32.orb
  val &&  = Word32.andb

  infix << >> || &&

  fun w32toReal w =
    let
      val i = Word32.toLargeIntX w
      val r = R.fromLargeInt i
    in
      if i < 0 then 4294967296.0 + r else r
    end

  fun randWord rnd = rnd ()

  fun randReal rnd =
    let
      val y = rnd ()
      val x = w32toReal y
    in
      x / 4294967295.0
    end
 
  val N      = 624
  val M      = 397
  val NM     = N - M
  val N_min1 = N - 1
  val M_min1 = M - 1
  val zero   = 0.0

  val AINIT1 : Word32.word = 0w19650218
  val AINIT2 : Word32.word = 0w1664525
  val AINIT3 : Word32.word = 0w1566083941

  val SGEN : Word32.word = 0w1812433253
  val SGENOLD : Word32.word = 0w69069

  val MATRIX_A   : Word32.word = 0wx9908b0df (* Constant vector a *)
  val UPPER_MASK : Word32.word = 0wx80000000 (* Most significant w-r bits *)
  val LOWER_MASK : Word32.word = 0wx7fffffff (* Least significant r bits *)

  val TEMPERING_MASK_B : Word32.word = 0wx9d2c5680  (* Tempering parameters *)
  val TEMPERING_MASK_C : Word32.word = 0wxefc60000

  fun TEMPERING_SHIFT_U y = y >> 0w11
  fun TEMPERING_SHIFT_S y = y << 0w7
  fun TEMPERING_SHIFT_T y = y << 0w15
  fun TEMPERING_SHIFT_L(y:Word32.word):Word32.word = y >> 0w18

  val mag01 = A.fromList [0w0, MATRIX_A]

  fun sgenold (seed) : state =
    let
      val (mt,mti) : state = (A.array(N,0w0), ref N)

      fun aux i =
          if i = N then ()
          else
            (A.update (mt, i, SGENOLD * A.sub (mt, i - 1));
            aux (i + 1))
    in
      A.update (mt, 0, seed);
      aux 1;
      mti := N;
      (mt,mti)
    end

  fun sgenrand (seed) : state =
    let
      val (mt,mti) : state = (A.array(N,0w0), ref N)

      fun aux i =
          if i = N then ()
          else
            (A.update (mt, i, SGEN * (A.sub (mt, i - 1) ^
              (A.sub (mt, i - 1) >> 0w30) ) + Word32.fromInt i);
            aux (i + 1))
    in
      A.update (mt, 0, seed);
      aux 1;
      mti := N;
      (mt,mti)
    end

  fun sarray (init_key) =
    let
      val key_length = A.length init_key
      val k = if N > key_length then N else key_length

      val (mt,mti) : state = sgenrand (AINIT1)

      fun lup1 (i,j,k) =
        let
          val ai = A.sub (mt, i)
          val ai1 = A.sub (mt, i - 1)
        in
          if k = 0 then (i)
          else
            ((A.update (mt, i, ((ai ^ ((ai1 ^ (ai1 >> 0w30)) * AINIT2))
                + A.sub (init_key, j) ) + Word32.fromInt j));
            if j + 1 >= key_length then
              (if i + 1 >= N then
                (A.update (mt, 0, A.sub(mt,N-1)); lup1 (1, 0, k - 1))
              else (lup1 (i + 1, 0, k - 1)))
            else
              (if i + 1 >= N then
                (A.update (mt, 0, A.sub(mt,N-1)); lup1 (1, j+1, k - 1))
              else (lup1 (i + 1, j+1, k - 1))))
        end

      fun lup2 (i,k) =
        let
          val ai = A.sub (mt, i)
          val ai1 = A.sub (mt, i - 1)
        in
          if k = 0 then ()
          else
            (A.update (mt, i, (ai ^ ((ai1 ^ (ai1 >> 0w30)) * AINIT3))
              - Word32.fromInt i);
            if i + 1 >= N then
              (A.update (mt, 0, A.sub(mt,N-1)); lup2 (1, k - 1))
            else (lup2 (i + 1, k - 1)))
        end

    in
      lup2 (lup1 (1, 0, k), N - 1);
      A.update (mt, 0, 0wx80000000);
      (mt,mti)
    end


  fun rand st =
    let
      val (mt,mti) : state = st
      fun inc_mti () = mti := !mti + 1

      fun refill () =
        let
          fun compy (i, j) =
            let
              val y = (A.sub (mt, i) && UPPER_MASK) ||
                      (A.sub (mt, j) && LOWER_MASK)
            in
              (y, Word32.toInt (y && 0w1))
            end

          fun nvalUpd (y, kk, i, mgi) =
             A.update (mt, kk, A.sub (mt, i) ^ (y >> 0w1) ^ A.sub (mag01, mgi))

          fun aux kk =
            if kk = NM then ()
            else let
                val (y, ind) = compy (kk, kk + 1)
              in
                nvalUpd (y, kk, kk + M, ind);
                aux (kk + 1)
              end

          fun aux' kk =
            if kk = N_min1 then ()
            else let
                val (y, ind) = compy (kk, kk + 1)
              in
                nvalUpd (y, kk, kk - NM, ind);
                aux' (kk + 1)
              end
        in
          aux 0;
          aux' NM;
          let
            val (y, ind) = compy (N_min1, 0)
          in
            nvalUpd (y, N_min1, M_min1, ind);
            mti := 0
          end
        end
    in
      fn () =>
         (if !mti = N then refill () else ();
          let 
            val y:Word32.word = A.sub (mt, !mti) before inc_mti ()
            val t:Word32.word = (TEMPERING_SHIFT_U y:Word32.word)
            val y:Word32.word = y ^ t
            val y = y ^ ((TEMPERING_SHIFT_S y) && TEMPERING_MASK_B)
            val y = y ^ ((TEMPERING_SHIFT_T y) && TEMPERING_MASK_C)
            val y = y ^ (TEMPERING_SHIFT_L y)
          in
            y
          end)
    end

fun makeRandomGen(choice_num) = 
  let val state1 = sarray(Array.fromList([0wx123, 0wx234, 0wx345, 0wx456]))
      val rg = rand(state1)
      val rr = randReal
      val rc = Real.fromInt(choice_num)
  in
    (fn () => Real.ceil(Real.*(rc,(rr rg))))
  end

fun makeRealNumRandGen(r) = 
     let val state1 = sarray(Array.fromList([0wx1]))
         val rg = rand(state1)
         val rr = randReal
     in
       fn () => Real.*(r,(rr rg))
     end

local val f = makeRealNumRandGen(1.0)
in
   fun getRandomInt(k) = Real.ceil(Real.*(Real.fromInt(k),f()))
end

end
