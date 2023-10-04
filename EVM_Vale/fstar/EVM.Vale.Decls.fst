module EVM.Vale.Decls
open EVM.Machine_Basic
module S = EVM.Semantics_s
module L = EVM.Vale.Lemmas

let ins = S.ins
type ocmp = S.ocmp

type va_pbool = Vale.Def.PossiblyMonad.pbool
let va_ttrue () = Vale.Def.PossiblyMonad.ttrue
let va_ffalse = Vale.Def.PossiblyMonad.ffalse
let va_pbool_and x y = Vale.Def.PossiblyMonad.((&&.)) x y

let mul_nat_helper x y =
  FStar.Math.Lemmas.nat_times_nat_is_nat x y

type va_fuel = nat
let va_fuel_default () = 0

let get_reason p =
  match p with
  | Vale.Def.PossiblyMonad.Ok () -> None
  | Vale.Def.PossiblyMonad.Err reason -> Some reason

let va_cmp_eq o1 o2 = S.OEq o1 o2
let va_cmp_ne o1 o2 = S.ONe o1 o2
let va_cmp_le o1 o2 = S.OLe o1 o2
let va_cmp_ge o1 o2 = S.OGe o1 o2
let va_cmp_lt o1 o2 = S.OLt o1 o2
let va_cmp_gt o1 o2 = S.OGt o1 o2  

let eval_code = L.eval_code

let va_ins_lemma c0 s0 = ()

let eval_ocmp = L.eval_ocmp
let valid_ocmp = Lemmas.valid_ocmp

unfold let va_eval_ins = L.eval_ins

let va_compute_merge_total = L.compute_merge_total
let va_lemma_merge_total b0 s0 f0 sM fM sN = L.lemma_merge_total b0 s0 f0 sM fM sN; L.compute_merge_total f0 fM
let va_lemma_empty_total = L.lemma_empty_total

let va_lemma_ifElse_total = L.lemma_ifElse_total
let va_lemma_ifElseTrue_total = Lemmas.lemma_ifElseTrue_total
let va_lemma_ifElseFalse_total = Lemmas.lemma_ifElseFalse_total