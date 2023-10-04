module EVM.Semantics_s
open FStar.Seq
open EVM.Machine_Basic
open FStar.Mul

type ins =
   // Stop and Arithmetic Operations
   | Stop   : ins
   | Add    : ins
   | Mul    : ins 
   | Mod    : ins
   | Sub    : ins 
   // Comparison and Bitwise Logic Operations
   | Lt     : ins
   | Gt     : ins
   | Eq     : ins
   | IsZero : ins
   // KECCAK256
   | Keccak256 : ins // Not implemented accurately, deterministically changes the top of the stack to a different number
   // Environmental Information
   | Address: ins
   | Balance: ins
   | Caller : ins
   | CallValue: ins
   // Block Information
   | TimeStamp:   ins
   | SelfBalance: ins
   // Stack, Memory, Storage and Flow Operations 
   | Pop    : ins
   | MLoad  : ins
   | MStore : ins
   | SLoad  : ins
   | SStore : ins
   // Push Operations
   | Push   : v:nat256 -> ins
   // Duplication Operations
   | Dup    : k:nat{1 <= k && k <= 16} -> ins
   // Exchange Operations
   | Swap   : k:nat{1 <= k && k <= 16} -> ins
   // System operations
   | Call   : ins // Naively implemented to allow transfers
   | Return : ins
   | Revert : ins 
   | Invalid: ins
   | SelfDestruct: ins

type ocmp =
  | OEq: o1:operand -> o2:operand -> ocmp
  | ONe: o1:operand -> o2:operand -> ocmp
  | OLe: o1:operand -> o2:operand -> ocmp
  | OGe: o1:operand -> o2:operand -> ocmp
  | OLt: o1:operand -> o2:operand -> ocmp
  | OGt: o1:operand -> o2:operand -> ocmp

type code = precode ins ocmp
type codes = list code

// Global state
let eval_bal'  (ptr:address) (s:state) : nat256 = load_bal ptr s.bal
// Execution state
let eval_stor' (ptr:nat256) (s:state) : nat256 = load_stor ptr s.exec_s.stor
let eval_mem'  (ptr:nat) (s:state) : nat256 = load_mem  s.exec_s.mem ptr

let eval_stk_hd_zero (s:state) : stackCheck = let stack = s.exec_s.stk in 
  match length stack with 
    | 0 -> 2
    | _ -> if head stack = 0 then 1 else 0 

let eval_operand (o:operand) (s:state) : nat256 =
  match o with
    | OConst n -> n
    | OCheck -> eval_stk_hd_zero s
    | OMem m   -> eval_mem'  m s
    | OStor a  -> eval_stor' a s

let eval_ocmp (s:state) (c:ocmp) : bool =
  match c with
    | OEq o1 o2 -> eval_operand o1 s  = eval_operand o2 s
    | ONe o1 o2 -> eval_operand o1 s <> eval_operand o2 s
    | OLe o1 o2 -> eval_operand o1 s <= eval_operand o2 s
    | OGe o1 o2 -> eval_operand o1 s >= eval_operand o2 s
    | OLt o1 o2 -> eval_operand o1 s  < eval_operand o2 s
    | OGt o1 o2 -> eval_operand o1 s  > eval_operand o2 s    

// Global State
let update_bal' (ptr:address) (v:nat256) (s:state) : state =
  { s with bal = store_bal ptr v s.bal }

// Execution state
let update_stor' (ptr:nat256) (v:nat256) (s:state) : state = 
  { s with exec_s = { s.exec_s with stor = store_stor ptr v s.exec_s.stor } }
let update_mem'  (ptr:nat) (v:nat256) (s:state) : state = 
  { s with exec_s = { s.exec_s with mem  = store_mem s.exec_s.mem ptr v } }

let valid_operand (o:operand) (s:state) : bool =
  match o with 
    | OConst n -> true
    | OCheck -> 0 < length s.exec_s.stk // TODO Daniel: Also doing this check down the bottom, this might be redundant
    | OStor  n -> true
    | OMem   n -> true

let valid_ocmp (c:ocmp) (s:state) : bool =
  match c with
    | OEq o1 o2 -> valid_operand o1 s && valid_operand o2 s
    | ONe o1 o2 -> valid_operand o1 s && valid_operand o2 s
    | OLe o1 o2 -> valid_operand o1 s && valid_operand o2 s
    | OGe o1 o2 -> valid_operand o1 s && valid_operand o2 s
    | OLt o1 o2 -> valid_operand o1 s && valid_operand o2 s
    | OGt o1 o2 -> valid_operand o1 s && valid_operand o2 s    

let update_operand (o:operand) (v:nat256) (s:state) : state =
  match o with
    | OConst _ -> {s with ok = false}
    | OCheck ->   {s with ok = false}
    | OMem  m -> update_mem'  (eval_mem'  m s) v s
    | OStor a -> update_stor' (eval_stor' a s) v s

// Define a stateful monad to simplify defining the instruction semantics
let st (a:Type) = state -> a & state

unfold
let return (#a:Type) (x:a) :st a =
  fun s -> x, s

unfold
let bind (#a:Type) (#b:Type) (m:st a) (f:a -> st b) :st b =
fun s0 ->
  let x, s1 = m s0 in
  let y, s2 = f x s1 in
  y, {s2 with ok=s0.ok && s1.ok && s2.ok}

unfold
let get :st state =
  fun s -> s, s

unfold
let pop :st nat256 = 
  fun s -> 
    match s.status with
      | ACTIVE ->  
          if empty s.exec_s.stk
          then 
            0, {s with ok = false} 
          else 
            (index s.exec_s.stk 0), { s with exec_s = { s.exec_s with stk = (slice s.exec_s.stk 1 (length s.exec_s.stk)) } }
      | _ -> 0, s  

unfold 
let push (v:nat256) : st unit  =
  fun s ->
    match s.status with 
      | ACTIVE -> 
          if full s.exec_s.stk 
          then 
            (), {s with ok = false} 
          else
            (), { s with exec_s = { s.exec_s with stk = (cons v s.exec_s.stk) } }
      | _ -> (), s      

unfold 
let peek : st nat =
  fun s ->
    match s.status with 
      | ACTIVE ->
          if empty s.exec_s.stk
          then 
            0, {s with ok = false} 
          else 
            (index s.exec_s.stk 0), s       
      | _ -> 0, s 

unfold 
let dup (k:nat{1 <= k && k <= 16}) : st unit =
  fun s ->
    match s.status with
      | ACTIVE ->
          let len = length s.exec_s.stk in
          if k - 1 < len && not_full s.exec_s.stk
          then 
            (let stk' = cons (index s.exec_s.stk (k - 1)) s.exec_s.stk in
            (), { s with exec_s = { s.exec_s with stk = stk' } })
          else
            (), { s with ok = false }
      | _ -> (), s      

unfold 
let swap (k:nat{1 <= k && k <= 16}) : st unit =
  fun s ->
    match s.status with
      | ACTIVE ->
          let len = length s.exec_s.stk in
          if k < len && 1 < len  
          then 
            (let stk' = Seq.swap s.exec_s.stk 0 k in
            (), { s with exec_s = { s.exec_s with stk = stk' } })
          else
            (), { s with ok = false }
      | _ -> (), s

unfold
let end_invalid (data:option (seq nat256)): st unit = 
  fun s ->
    match s.status with 
      | ACTIVE ->
        (), {s with status=END_INVALID; returnData = data} 
      | _ -> (), s    

unfold
let end_valid (data:option (seq nat256)): st unit = 
  fun s -> 
    match s.status with
      | ACTIVE ->
          (), {s with status = END_VALID; returnData = data}         
      | _ -> (), s   

unfold
let end_selfdestruct : st unit = 
  fun s -> 
    match s.status with
      | ACTIVE ->
          (), {s with status = END_SELFDESTRUCT; returnData = None}         
      | _ -> (), s           

unfold
let update_stor (ptr:nat256) (v:nat256) : st unit =
  fun s ->
    match s.status with 
      | ACTIVE -> 
          (), update_stor' ptr v s
      | _ -> (), s    

unfold
let eval_stor (ptr:nat256) : st nat256 =
  fun s -> 
    match s.status with 
      | ACTIVE -> 
          (eval_stor' ptr s), s    
      | _ -> 0, s 

unfold
let update_mem (ptr:nat) (v:nat256) : st unit =
  fun s ->
    match s.status with 
      | ACTIVE -> 
          (), update_mem' ptr v s
      | _ -> (), s 

unfold
let eval_mem (ptr:nat) : st nat256 =
  fun s -> 
    match s.status with 
      | ACTIVE -> 
          (eval_mem' ptr s), s    
      | _ -> 0, s 

unfold
let eval_bal (ptr:address) : st nat256 =
  fun s -> 
    match s.status with 
      | ACTIVE -> 
          (eval_bal' ptr s), s    
      | _ -> 0, s 

unfold
let update_bal (ptr:address) (v:nat256) : st unit =
  fun s ->
    match s.status with 
      | ACTIVE -> 
          (), update_bal' ptr v s
      | _ -> (), s 

unfold
let set (s:state) :st unit =
  fun _ -> (), s

unfold
let fail :st unit =
  fun s -> (), {s with ok=false}

unfold
let check_imm (valid:bool) : st unit =
  if valid then
    return ()
  else
    fail

unfold
let check (valid: state -> bool) : st unit =
  s <-- get;
  if valid s then
    return ()
  else
    fail

unfold
let run (f:st unit) (s:state) : state = snd (f s)

let eval_ins (i:ins) : st unit =
  s <-- get;
  match i with 
    // Stop and Arithmetic Operations
    | Stop ->
      end_valid None   
    | Add -> 
        v0 <-- pop; 
        v1 <-- pop;
        push ((v0+v1) % pow2_256)
    | Mul ->
        v0 <-- pop;
        v1 <-- pop;
        push ((v0 * v1) % pow2_256)
    | Mod ->
        v0 <-- pop;
        v1 <-- pop;
        push (if v1 = 0 then 0 else (v0 % v1))
    | Sub ->
        v0 <-- pop;
        v1 <-- pop;
        push (if v1 <= v0 then v0 - v1 else (v0 - v1) % pow2_256) // Redundant if statement helps verification
    // Comparison and Bitwise Logic Operations    
    | Lt ->
        v0 <-- pop;
        v1 <-- pop;
        if v0 < v1 
        then 
          push 1
        else
          push 0
    | Gt -> 
        v0 <-- pop;
        v1 <-- pop;
        if v0 > v1
        then 
          push 1
        else
          push 0
    | Eq ->
        v0 <-- pop;
        v1 <-- pop;
        if v0 = v1
        then 
          push 1
        else
          push 0
    | IsZero ->
        v0 <-- pop;
        if v0 = 0
        then 
          push 1
        else 
          push 0
    // KECCAK256
    | Keccak256 ->
        v0 <-- pop;
        push (Keccak.keccak v0)
    // Environmental Information
    | Address ->
      push (s.env.actor)
    | Balance ->
        ptr <-- pop;
        b <-- eval_bal (ptr % pow2_160);
        push b    
    | Caller ->
        push (s.env.sender)    
    | CallValue ->
        push (s.env.value)    
    // Block Information
    | TimeStamp ->
        push(s.timeStamp)
    | SelfBalance -> 
        bal <-- eval_bal s.env.actor;
        push bal    
    // Stack, Memory, Storage and Flow Operations 
    | Pop -> 
        _ <-- pop;
        return ()     
    | MLoad -> 
        ptr <-- pop;
        v <-- eval_mem ptr; 
        push v
    | MStore ->
        ptr <-- pop;
        v <-- pop;
        update_mem ptr v 
    | SLoad -> 
        ptr <-- pop;
        v <-- eval_stor ptr; 
        push v
    | SStore ->
        ptr <-- pop;
        v <-- pop;
        update_stor ptr v
    // Push Operations
    | Push v -> 
        push v  
    // Duplication Operations
    | Dup k ->
        dup k
    // Exchange Operations
    | Swap k ->
        swap k   
    // System operations
    | Call ->
      callee <-- pop;
      amount <-- pop;
      bal_actor <-- eval_bal s.env.actor;
      bal_callee <-- eval_bal (callee % pow2_160);
      if bal_actor < amount
      then
        push 0
      else (
        _ <-- update_bal s.env.actor (bal_actor - amount);
        _ <-- update_bal (callee % pow2_160) ((bal_callee + amount) % pow2_256); 
        _ <-- push 1;
        check_imm (bal_callee + amount < pow2_256) // Overflow check on balance transfer
      )
    | Return ->
      ptr  <-- pop;
      size <-- pop;
      end_valid (Some (make_return_data s.exec_s.mem ptr size))     
    | Revert ->
      ptr  <-- pop;
      size <-- pop;
      end_invalid (Some (make_return_data s.exec_s.mem ptr size)) 
    | Invalid ->
      end_invalid None    
    | SelfDestruct ->
        ben   <-- pop;
        bal_a <-- eval_bal s.env.actor;
        bal_b <-- eval_bal (ben % pow2_160);
        _   <-- update_bal s.env.actor 0;
        _   <-- update_bal (ben % pow2_160) ((bal_a + bal_b) % pow2_256); 
        _ <-- end_selfdestruct;
        check_imm (bal_a + bal_b < pow2_256) // Overflow check on balance transfer

// Evaluating ocmp pops comparator off stack, fail if stack is empty
let run_ocmp (s:state) (c:ocmp) : state & bool =
  match (length s.exec_s.stk) with 
    | 0 -> ( {s with ok=false} , false)
    | _ -> 
      ({s with exec_s = { s.exec_s with stk = tail s.exec_s.stk } }, eval_ocmp s c)        

(*
 * These functions return an option state
 * eval_code of an INACTIVE state always passes state on unchanged
 *)
let rec eval_code (c:code) (fuel:nat) (s:state) : Tot (option state) (decreases %[fuel; c]) =
  match s.status with
  | ACTIVE -> (  
      match c with
      | Ins ins ->
        Some (run (eval_ins ins) s)
      | Block l ->
        eval_codes l fuel s
      | IfElse cond ifTrue ifFalse  ->
        let (s, b) = run_ocmp s cond in
        if b then eval_code ifTrue fuel s else eval_code ifFalse fuel s 
    )
  | _ -> Some s    
and eval_codes (l:codes) (fuel:nat) (s:state) : Tot (option state) (decreases %[fuel; l]) =
  match s.status with
  | ACTIVE -> (
      match l with
      | []   -> Some s
      | c::tl ->
        let s_opt = eval_code c fuel s in
        if None? s_opt then None else eval_codes tl fuel (Some?.v s_opt) 
    )
  | _ -> Some s      