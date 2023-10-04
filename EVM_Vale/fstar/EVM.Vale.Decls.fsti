module EVM.Vale.Decls
open FStar.Seq
open EVM.Machine_Basic
open FStar.Mul
// Do not reference EVM.Semantics_s

// Type Aliases
let va_int_at_least (k:int) = i:int{i >= k}
let va_int_at_most (k:int) = i:int{i <= k}
let va_int_range (k1 k2:int) = i:int{k1 <= i /\ i <= k2}
val ins : Type0
val ocmp: Type0
unfold let va_code = precode ins ocmp 
unfold let va_codes = list va_code 
unfold let cmp_operand = operand 
unfold let src_operand = operand

let va_const_cmp (o:nat256) : cmp_operand = OConst o 

val va_pbool : Type0
val va_ttrue (_:unit) : va_pbool
val va_ffalse (reason:string) : va_pbool
val va_pbool_and (x y:va_pbool) : va_pbool

val mul_nat_helper (x y:nat) : Lemma (x * y >= 0)
unfold let va_mul_nat (x y:nat) : nat =
  mul_nat_helper x y;
  x * y

unfold let va_operand_src  = operand
unfold let va_operand_Stor = operand
unfold let va_operand_Mem  = operand
unfold let va_state = state  
val va_fuel : Type0

// Constructors
unfold let va_const_src (n:nat256) = OConst n
unfold let va_op_cmp_hdStkZero (something:unit) :cmp_operand = OCheck
unfold let va_coerce_Stor_to_cmp (ptr:va_operand_Stor) : cmp_operand = ptr
unfold let va_coerce_Stor_to_src (ptr:va_operand_Stor) : src_operand = ptr
unfold let va_coerce_Mem_to_cmp (ptr:va_operand_Mem) : cmp_operand = ptr
unfold let va_coerce_Mem_to_src (ptr:va_operand_Mem) : src_operand = ptr
unfold let va_opr_code_Stor (ptr:nat256) : operand = OStor ptr
unfold let va_opr_code_Mem  (ptr:nat) : operand = OMem ptr

// Evaluation
// Repeating these defs so this file doesn't directly reference semantics
let eval_stor' (ptr:nat256) (s:state) : nat256 = load_stor ptr s.exec_s.stor
let eval_mem'  (ptr:nat)     (s:state) : nat256 = load_mem  s.exec_s.mem ptr
let eval_stk_hd_zero (s:state) : stackCheck = let stack = s.exec_s.stk in 
  match length stack with 
    | 0 -> 2
    | _ -> if head stack = 0 then 1 else 0 
let eval_operand (o:operand) (s:state) : nat =
  match o with
    | OConst n -> n
    | OCheck -> eval_stk_hd_zero s
    | OMem m   -> eval_mem'  m s
    | OStor a  -> eval_stor' a s

// Getters
val get_reason (p:va_pbool) : option string  // From HACL Star
unfold let va_get_ok  (s:va_state) : bool    = s.ok
unfold let va_get_stk (s:va_state) : execStack = s.exec_s.stk
unfold let va_get_status (s:va_state) : execStatus = s.status
unfold let va_get_sender (s:va_state) : address = s.env.sender
unfold let va_get_actor (s:va_state) : address = s.env.actor
unfold let va_get_value  (s:va_state) : nat = s.env.value
unfold let va_get_hdStkZero  (s:va_state) : stackCheck = let stack = s.exec_s.stk in 
  match length stack with 
    | 0 -> 2
    | _ -> if head stack = 0 then 1 else 0
unfold let va_get_timeStamp (s:va_state) : nat = s.timeStamp       
unfold let va_get_returnData (s:va_state) : option (seq nat256) = s.returnData 


// Update helpers
let va_upd_ok  (ok:bool)     (s:state) : state = { s with ok = ok }
let va_upd_stk (stk:execStack) (s:state) : state = { s with exec_s = { s.exec_s with stk = stk } }
let va_upd_stor (stor:storage) (s:state) : state = { s with exec_s = { s.exec_s with stor = stor } } 
let va_upd_mem  (mem :memory)  (s:state) : state = { s with exec_s = { s.exec_s with mem = mem } } 
let va_upd_bal  (bal:balances) (s:state) : state = { s with bal = bal } 
let va_upd_status (a:execStatus) (s:state) : state = { s with status = a }
let va_upd_returnData (a:option (seq nat256)) (s:state) : state = { s with returnData = a }

// Framing: va_update_foo means the two states are the same except for foo
unfold let va_update_ok (sM:va_state) (sK:va_state): va_state = va_upd_ok sM.ok sK 
unfold let va_update_stk (sM:va_state) (sK:va_state): va_state = va_upd_stk sM.exec_s.stk sK  
unfold let va_update_stor (sM:va_state) (sK:va_state): va_state = va_upd_stor sM.exec_s.stor sK
unfold let va_update_mem  (sM:va_state) (sK:va_state): va_state = va_upd_mem  sM.exec_s.mem  sK 
unfold let va_update_bal  (sM:va_state) (sK:va_state): va_state = va_upd_bal  sM.bal  sK 
unfold let va_update_status (sM:va_state) (sK:va_state) : va_state = va_upd_status sM.status sK
unfold let va_update_returnData (sM:va_state) (sK:va_state) : va_state = va_upd_returnData sM.returnData sK

unfold let va_update_execStack (stk:execStack) (i:nat{i < length stk}) (v:nat256):execStack = Seq.upd stk i v 

// va_codes constructors
let va_CNil () : va_codes = [] // TODO Daniel: Type annotations might be needed
let va_CCons (hd:va_code) (tl:va_codes) : va_codes  = hd::tl 
let va_get_stor (s:va_state) : storage = s.exec_s.stor
let va_get_mem  (s:va_state) : memory  = s.exec_s.mem
let va_get_bal  (s:va_state) : balances  = s.bal

// va_code constructors
let va_Block (block:va_codes) : Tot va_code = Block block
unfold let va_IfElse (ifCond:ocmp) (ifTrue:va_code) (ifFalse:va_code) : va_code = IfElse ifCond ifTrue ifFalse

val va_cmp_eq (o1:operand) (o2:operand) : ocmp 
val va_cmp_ne (o1:operand) (o2:operand) : ocmp 
val va_cmp_le (o1:operand) (o2:operand) : ocmp 
val va_cmp_ge (o1:operand) (o2:operand) : ocmp
val va_cmp_lt (o1:operand) (o2:operand) : ocmp
val va_cmp_gt (o1:operand) (o2:operand) : ocmp

unfold let va_get_block (c:va_code{Block? c}) : GTot va_codes = Block?.block c
unfold let va_get_ifCond (c:va_code{IfElse? c}) : ocmp = IfElse?.ifCond c
unfold let va_get_ifTrue (c:va_code{IfElse? c}) : va_code = IfElse?.ifTrue c
unfold let va_get_ifFalse (c:va_code{IfElse? c}) : va_code = IfElse?.ifFalse c

let va_state_eq (s0:va_state) (s1:va_state) : Type = 
  s0.ok = s1.ok /\
  s0.status = s1.status /\ 
  // Global State
  s0.bal == s1.bal /\
  // Environment
  s0.env.actor   == s1.env.actor   /\
  s0.env.sender  == s1.env.sender  /\
  s0.env.value   == s1.env.value   /\
  // Transaction state
  s0.timeStamp == s1.timeStamp /\
  // Execution state
  s0.exec_s.stk = s1.exec_s.stk /\ 
  s0.exec_s.mem  == s1.exec_s.mem /\
  s0.exec_s.stor == s1.exec_s.stor /\
  // Return Data
  s0.returnData = s1.returnData

val eval_code (c:va_code) (s0:va_state) (f0:va_fuel) (sN:va_state) : Type0

unfold let va_hd = Cons?.hd
unfold let va_tl = Cons?.tl // TODO Daniel: This might be too simple

let va_reveal_opaque (s:string) = norm_spec [zeta; delta_only [s]]

let va_require_total (b0:va_code) (c:va_code) (s0:va_state) : Type0 =
  b0 == c

let va_ensure_total (b0:va_code) (s0:va_state) (s1:va_state) (f1:va_fuel) : Type =
    eval_code b0 s0 f1 s1

val va_ins_lemma (c0:va_code) (s0:va_state) : Lemma
  (requires True)
  (ensures True) // TODO Daniel: Could be expanded upon if necessary

val eval_ocmp : s:va_state -> c:ocmp -> GTot bool
unfold let va_evalCond (b:ocmp) (s:va_state) : GTot bool = eval_ocmp s b

val valid_ocmp : c:ocmp -> s:va_state -> GTot bool

val va_compute_merge_total (f0:va_fuel) (fM:va_fuel) : va_fuel

val va_lemma_merge_total (b0:va_codes) (s0:va_state) (f0:va_fuel) (sM:va_state) (fM:va_fuel) (sN:va_state) : Ghost (fN:va_fuel)
  (requires
    Cons? b0 /\
    eval_code (Cons?.hd b0) s0 f0 sM /\
    eval_code (va_Block (Cons?.tl b0)) sM fM sN
  )
  (ensures (fun fN ->
    fN == va_compute_merge_total f0 fM /\
    eval_code (va_Block b0) s0 fN sN
  ))

val va_lemma_empty_total (s0:va_state) (bN:va_codes) : Ghost (va_state & va_fuel)
  (requires True)
  (ensures (fun (sM, fM) ->
    s0 == sM /\
    eval_code (va_Block []) s0 fM sM
  ))

val va_lemma_ifElse_total (ifb:ocmp) (ct:va_code) (cf:va_code) (s0:va_state) : Ghost (bool & va_state & va_state & va_fuel)
  (requires s0.status == ACTIVE ==> 0 < length s0.exec_s.stk) // ACTIVE => comparator on stack
  (ensures  (fun (cond, sM, sN, f0) ->
    (cond == eval_ocmp s0 ifb) /\ // The branching condidition is the evaluation of the guard
    (s0.status <> ACTIVE ==> sM == s0) /\ // INACTIVE => Stack and rest of state is unaltered
    (s0.status == ACTIVE  ==> sM == { s0 with exec_s = { s0.exec_s with stk = tail s0.exec_s.stk } }) // INACTIVE => resulting stack is tail of input stack
  ))    

val va_lemma_ifElseTrue_total (ifb:ocmp) (ct:va_code) (cf:va_code) (s0:va_state) (f0:va_fuel) (sM:va_state) : Lemma
  (requires
    eval_ocmp s0 ifb /\ // The guard is true
    (s0.status == ACTIVE ==> 0 < length s0.exec_s.stk) /\ // ACTIVE => comparator on stack
    (s0.status == ACTIVE ==> eval_code ct ({s0 with exec_s = {s0.exec_s with stk = tail s0.exec_s.stk}}) f0 sM) /\ // ACTIVE => resulting stack is tail of input stack
    (s0.status <> ACTIVE ==> eval_code ct s0 f0 sM) 
  )
  (ensures
    eval_code (IfElse ifb ct cf) s0 f0 sM
  )

val va_lemma_ifElseFalse_total (ifb:ocmp) (ct:va_code) (cf:va_code) (s0:va_state) (f0:va_fuel) (sM:va_state) : Lemma
   (requires
    (s0.status == ACTIVE ==> 0 < length s0.exec_s.stk) /\ // ACTIVE => comparator on stack
    not (eval_ocmp s0 ifb) /\ // The guard is false
    (s0.status == ACTIVE ==> eval_code cf ({s0 with exec_s = {s0.exec_s with stk = tail s0.exec_s.stk}}) f0 sM) /\ // ACTIVE => resulting stack is tail of input stack
    (s0.status <> ACTIVE ==> eval_code cf s0 f0 sM) 
  )
  (ensures
    eval_code (IfElse ifb ct cf) s0 f0 sM
  )