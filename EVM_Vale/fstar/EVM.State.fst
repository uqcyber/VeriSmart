module EVM.State
open EVM.Machine_Basic

unfold let state_equiv (s0:state) (s1:state) : Type0 =
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
  Seq.equal s0.exec_s.stk s1.exec_s.stk /\ 
  Seq.equal s0.exec_s.mem s1.exec_s.mem /\
  s0.exec_s.stor == s1.exec_s.stor /\
  // Return Data
  s0.returnData = s1.returnData

unfold let inactive_state_unchanged (s0:state) (s1:state) : Type0 =
  s0.status <> ACTIVE ==> state_equiv s0 s1 