module EVM.Vale.Lemmas
open EVM.Machine_Basic
module S = EVM.Semantics_s

#reset-options "--initial_fuel 5 --max_fuel 5 --z3rlimit 20"

let rec increase_fuel (c:code) (s0:state) (f0:fuel) (sN:state) (fN:fuel) : Lemma
  (requires eval_code c s0 f0 sN /\ f0 <= fN)
  (ensures eval_code c s0 fN sN)
  (decreases %[f0; c])
  =
  match s0.status with
  | ACTIVE -> (
      match c with
      | Ins ins -> ()
      | Block l -> increase_fuels l s0 f0 sN fN
      | IfElse cond t f ->
          let (s0, b) = S.run_ocmp s0 cond in
          if b then increase_fuel t s0 f0 sN fN else increase_fuel f s0 f0 sN fN
    )      
  | _ -> ()  
and increase_fuels (c:codes) (s0:state) (f0:fuel) (sN:state) (fN:fuel) : Lemma
  (requires eval_code (Block c) s0 f0 sN /\ f0 <= fN)
  (ensures eval_code (Block c) s0 fN sN)
  (decreases %[f0; c])
  =
  match s0.status with 
  | ACTIVE -> (
      match c with
      | [] -> ()
      | h::t ->
        (
          let Some s1 = S.eval_code h f0 s0 in
          increase_fuel h s0 f0 s1 fN;
          increase_fuels t s1 f0 sN fN
        )
    )
  | _ -> ()      

let lemma_cmp_eq s o1 o2 = ()
let lemma_cmp_ne s o1 o2 = ()
let lemma_cmp_le s o1 o2 = ()
let lemma_cmp_ge s o1 o2 = ()
let lemma_cmp_lt s o1 o2 = ()
let lemma_cmp_gt s o1 o2 = ()    

let compute_merge_total (f0:fuel) (fM:fuel) =
    if f0 > fM then f0 else fM    

let lemma_merge_total (b0:codes) (s0:state) (f0:fuel) (sM:state) (fM:fuel) (sN:state) =
  let f = if f0 > fM then f0 else fM in
  increase_fuel (Cons?.hd b0) s0 f0 sM f;
  increase_fuel (Block (Cons?.tl b0)) sM fM sN f    

let lemma_empty_total (s0:state) (bN:codes) = 
    (s0, 0)   

let lemma_ifElse_total (ifb:ocmp) (ct:code) (cf:code) (s0:state) =
 if s0.status = ACTIVE
  then
    (eval_ocmp s0 ifb, ({s0 with exec_s = {s0.exec_s with stk = tail s0.exec_s.stk}}), s0, 0)
  else 
    (eval_ocmp s0 ifb, s0, s0, 0)   

let lemma_ifElseTrue_total (ifb:ocmp) (ct:code) (cf:code) (s0:state) (f0:fuel) (sM:state) =
  ()

let lemma_ifElseFalse_total (ifb:ocmp) (ct:code) (cf:code) (s0:state) (f0:fuel) (sM:state) =
  ()
