module EVM.Vale.Lemmas
open FStar.Seq
open EVM.Machine_Basic
module S = EVM.Semantics_s

unfold let code = S.code
unfold let codes = S.codes
unfold let ocmp = S.ocmp
unfold let fuel = nat


let eval_code (c:code) (s0:state) (f0:fuel) (s1:state) : Type0 =
    Some s1 == S.eval_code c f0 s0 

let eval_ins (c:code) (s0:state) : Pure (state & fuel)
    (requires Ins? c)
    (ensures fun (sM, f0) ->
        eval_code c s0 f0 sM
    ) =
    let f0 = 0 in 
    let (Some sM) = S.eval_code c f0 s0 in
    (sM, f0)

let eval_ocmp (s:state) (c:ocmp) : bool = S.eval_ocmp s c

let valid_ocmp (c:ocmp) (s:state) : bool = S.valid_ocmp c s

let ensure_valid_ocmp (c:ocmp) (s:state) : state = S.run (S.check (S.valid_ocmp c)) s

val lemma_cmp_eq : s:state -> o1:operand -> o2:operand -> Lemma
  (ensures eval_ocmp s (S.OEq o1 o2) <==> S.eval_operand o1 s == S.eval_operand o2 s)
  [SMTPat (eval_ocmp s (S.OEq o1 o2))]

val lemma_cmp_ne : s:state -> o1:operand -> o2:operand -> Lemma
  (ensures eval_ocmp s (S.ONe o1 o2) <==> S.eval_operand o1 s <> S.eval_operand o2 s)
  [SMTPat (eval_ocmp s (S.ONe o1 o2))]

val lemma_cmp_le : s:state -> o1:operand -> o2:operand -> Lemma
  (ensures eval_ocmp s (S.OLe o1 o2) <==> S.eval_operand o1 s <= S.eval_operand o2 s)
  [SMTPat (eval_ocmp s (S.OLe o1 o2))]

val lemma_cmp_ge : s:state -> o1:operand -> o2:operand -> Lemma
  (ensures eval_ocmp s (S.OGe o1 o2) <==> S.eval_operand o1 s >= S.eval_operand o2 s)
  [SMTPat (eval_ocmp s (S.OGe o1 o2))]

val lemma_cmp_lt : s:state -> o1:operand -> o2:operand -> Lemma
  (ensures eval_ocmp s (S.OLt o1 o2) <==> S.eval_operand o1 s < S.eval_operand o2 s)
  [SMTPat (eval_ocmp s (S.OLt o1 o2))]

val lemma_cmp_gt : s:state -> o1:operand -> o2:operand -> Lemma
  (ensures eval_ocmp s (S.OGt o1 o2) <==> S.eval_operand o1 s > S.eval_operand o2 s)
  [SMTPat (eval_ocmp s (S.OGt o1 o2))]

val compute_merge_total (f0:fuel) (fM:fuel) : fuel

val lemma_merge_total (b0:codes) (s0:state) (f0:fuel) (sM:state) (fM:fuel) (sN:state) : Lemma
  (requires
    Cons? b0 /\
    eval_code (Cons?.hd b0) s0 f0 sM /\
    eval_code (Block (Cons?.tl b0)) sM fM sN
  )
  (ensures eval_code (Block b0) s0 (compute_merge_total f0 fM) sN)

// TODO Daniel: Could be issues with eqType on state being prop
val lemma_empty_total (s0:state) (bN:codes) : Pure (state & fuel)
    (requires True)
    (ensures (fun (sM, fM) -> 
        s0 == sM /\
        eval_code (Block []) s0 fM sM
    ))

val lemma_ifElse_total (ifb:ocmp) (ct:code) (cf:code) (s0:state) : Pure (bool & state & state & fuel)
  (requires s0.status == ACTIVE ==> 0 < length s0.exec_s.stk) // ACTIVE => comparator on stack
  (ensures  (fun (cond, sM, sN, f0) ->
    (cond == eval_ocmp s0 ifb) /\ // The branching condidition is the evaluation of the guard
    (s0.status <> ACTIVE ==> sM == s0) /\ // INACTIVE => Stack and rest of state is unaltered
    (s0.status == ACTIVE ==> sM == { s0 with exec_s = { s0.exec_s with stk = tail s0.exec_s.stk } }) // INACTIVE => resulting stack is tail of input stack
  ))   

val lemma_ifElseTrue_total (ifb:ocmp) (ct:code) (cf:code) (s0:state) (f0:fuel) (sM:state) : Lemma
  (requires
    eval_ocmp s0 ifb /\ // The guard is true
    (s0.status == ACTIVE ==> 0 < length s0.exec_s.stk) /\ // ACTIVE => comparator on stack
    (s0.status == ACTIVE ==> eval_code ct ({s0 with exec_s = {s0.exec_s with stk = tail s0.exec_s.stk}}) f0 sM) /\ // ACTIVE => resulting stack is tail of input stack
    (s0.status <> ACTIVE ==> eval_code ct s0 f0 sM) 
  )
  (ensures
    eval_code (IfElse ifb ct cf) s0 f0 sM
  )

val lemma_ifElseFalse_total (ifb:ocmp) (ct:code) (cf:code) (s0:state) (f0:fuel) (sM:state) : Lemma
  (requires
    (s0.status == ACTIVE ==> 0 < length s0.exec_s.stk) /\ // ACTIVE => comparator on stack
    not (eval_ocmp s0 ifb) /\ // The guard is false
    (s0.status == ACTIVE ==> eval_code cf ({s0 with exec_s = {s0.exec_s with stk = tail s0.exec_s.stk}}) f0 sM) /\ // ACTIVE => resulting stack is tail of input stack
    (s0.status <> ACTIVE ==> eval_code cf s0 f0 sM) 
  )
  (ensures
    eval_code (IfElse ifb ct cf) s0 f0 sM
  )
