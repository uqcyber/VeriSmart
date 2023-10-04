module EVM.Machine_Basic
open FStar.Seq 

unfold let pow2_160 = 0x10000000000000000000000000000000000000000
unfold let pow2_256 = 0x10000000000000000000000000000000000000000000000000000000000000000 

type nat256 = n:nat {0 <= n && n < 0x10000000000000000000000000000000000000000000000000000000000000000}
type address = n:nat {0 <= n && n < 0x10000000000000000000000000000000000000000} 

type memory  = Seq.seq nat256 
type storage = Map.t nat256 nat256
type balances = Map.t address nat256

// Truncted representation of execution environment
type execEnv = {
  actor:  address;  // The owner of the code that is executing
  sender: address;  // The caller's address
  value:  nat256; // The amount of Wei transferred with the call
}

type execStack = s:seq nat256{0 <= length s && length s <= 1024}
type stackCheck = n:nat{0 <= n && n <= 2} 

// Representation of the execution state
noeq type execState = { 
  stk:  execStack;
  mem:  memory; 
  stor: storage; 
  hdStkZero: stackCheck // 0 -> 1, 1 -> 0, NaN -> 2, a virtual representation of the head of the stack, this value is never actually written or read (check Decls)
} 

// The status of the program
type execStatus =
  | ACTIVE: execStatus
  | END_VALID: execStatus
  | END_INVALID: execStatus
  | END_SELFDESTRUCT: execStatus 

noeq type state = {
  ok:     bool;
  status: execStatus;
  env:    execEnv;
  bal:    balances; 
  exec_s: execState; 
  timeStamp: nat256;
  returnData: option (Seq.seq nat256)
}   

let expand (mem:memory) (ptr:nat) : memory =
  if ptr < Seq.length mem
  then 
    mem
  else 
    let diff = ptr - Seq.length mem in
    Seq.append mem (Seq.create (diff + 1) 0)

let load_mem (mem:memory) (ptr:nat): nat256 =
  if ptr < Seq.length mem
  then 
    Seq.index mem ptr
  else 
    0

let store_mem (mem:memory) (ptr:nat) (v:nat256): memory =
  if ptr < Seq.length mem
  then 
    Seq.upd mem ptr v
  else 
    let exp_mem = expand mem ptr in
    Seq.upd exp_mem ptr v  

let make_return_data (mem:memory) (ptr:nat) (size:nat) =
  let end_ptr = ptr + size in
  if end_ptr < Seq.length mem
  then 
    Seq.slice mem ptr end_ptr 
  else
    let exp_mem = expand mem end_ptr in
    Seq.slice exp_mem ptr end_ptr 

let load_stor (ptr:nat256) (s:storage) : nat256 =
  Map.sel s ptr

let store_stor (ptr:nat256) (v:nat256) (s:storage) : storage =
  Map.upd s ptr v

let load_bal (addr:address) (b:balances) : nat256 =
  Map.sel b addr 

let store_bal (addr:address) (v:nat256) (b:balances) : balances =
  Map.upd b addr v

// Maps all values in storage to provided value
let init_storage (s:storage) (v:nat256) : storage = Map.map_val (fun _ -> v) s 

type operand = 
  | OConst: n:nat256 -> operand
  | OCheck: operand
  | OMem:   m:nat -> operand
  | OStor:  s:nat256 -> operand

type precode (t_ins:Type0) (t_ocmp:Type0) =
  | Ins: ins:t_ins -> precode t_ins t_ocmp
  | Block: block:list (precode t_ins t_ocmp) -> precode t_ins t_ocmp
  | IfElse: ifCond:t_ocmp -> ifTrue:precode t_ins t_ocmp -> ifFalse:precode t_ins t_ocmp -> precode t_ins t_ocmp

// Vale will error because of execStack so the functions need to be wrapped
unfold let len (s:execStack):nat = length s
unfold let eql (s1:execStack) (s2:execStack) = equal s1 s2
unfold let hd  (s:execStack{0 < length s}):nat256 = head s
unfold let tl  (s:execStack{0 < length s}):execStack = tail s
unfold let ind (s:execStack) (i:nat{i < length s}):nat = index s i
unfold let cns (x:nat256) (xs:execStack{length xs < 1024}):execStack = cons x xs
unfold let rem (s:execStack{0 < length s}) (n:nat{n <= length s}):execStack = slice s n (length s)
unfold let slce (s:execStack) (i:nat{0 <= i && i <= len s}) (j:nat{i <= j && j <= len s}) :execStack = slice s i j
unfold let updt (s:execStack{0 < length s}) (n:nat{n < length s}) (a:nat256):execStack = upd s n a

let full (stk:execStack) : bool = length stk = 1024 
let empty (stk:execStack) : bool = length stk = 0
let not_full (stk:execStack) : bool = length stk < 1024
let not_empty (stk:execStack) : bool = 0 < length stk
