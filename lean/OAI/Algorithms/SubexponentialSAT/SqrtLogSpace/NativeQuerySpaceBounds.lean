import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeQueryInputBounds
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryCorrect
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryStreamSpaceBudgets

/-! Polynomial space for the actual complete marked and accepted queries.
The input cap is the same immutable leaf bound used by preparation. The
conditioned stream, high loop and whole-word return use their own proved
prefix bounds; no query runtime or number of attained tuples enters space. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeQuerySpaceBounds

open SqrtLog LeafParametersProgram NativeQueryInputBounds
open CostAssembly.Polynomial

/-- Exactly the prefix expression of the completed native query, with the
source and field allowances chosen by the actual literal-query caller. -/
def querySpace (q : LeafQueryFrontend.Query)
    (Cp dp Cn dn Cl dl Cf df N L k n h t d J f B : ℕ) : ℕ :=
  let S := sourceCap Cn dn Cl dl N L k
  let P := preparedCap Cp dp Cn dn Cl dl Cf df N L k
  let A := 12*P+4*N+6
  let T := A+S+2
  HighQueryCorrect.space q S (frontendCap Cf df L k) (S+f) B (Cp*(S+f+1)^dp)
    (HighQueryCorrect.loopSpace n h t d J A T) (QueryHeadBudgets.compact A)

/-- A fixed polynomial sum dominates the nested physical prefix maxima. -/
def envelope (C e W : ℕ) : ℕ :=
  1000*(W+1)+1000*C*(30*(W+1))^e

private theorem envelope_mono (C e W U : ℕ) (h : W ≤ U) :
    envelope C e W ≤ envelope C e U := by
  unfold envelope
  gcongr

/-- The field-cardinality allowance is A+S+2 because the real serialized
port44 stores 3^d-2 and is bounded by S. The source dimensions t,d,J come
from the same produced numeric bank. Suspended words remain a separate max. -/
theorem envelope_bound : ∃ C e : ℕ,
    ∀ (Cp dp Cn dn Cl dl Cf df N L k : ℕ) (q : LeafQueryFrontend.Query)
      (n h t d J f B : ℕ),
      BinaryArithmetic.toNat q.ambient = n → n ≤ N → h ≤ n →
      t ≤ sourceCap Cn dn Cl dl N L k →
      d ≤ sourceCap Cn dn Cl dl N L k →
      J ≤ sourceCap Cn dn Cl dl N L k → f ≤ frontendCap Cf df L k →
      querySpace q Cp dp Cn dn Cl dl Cf df N L k n h t d J f B ≤
        max (envelope C e (sourceCap Cn dn Cl dl N L k+frontendCap Cf df L k+
          preparedCap Cp dp Cn dn Cl dl Cf df N L k+4*N+6)) B := by
  obtain ⟨C,e,hstream⟩ := QueryStreamSpaceBudgets.complete_polynomial
  refine ⟨C,e,?_⟩
  intro Cp dp Cn dn Cl dl Cf df N L k q n h t d J f B hqn hn hh ht hd hJ hf
  let S := sourceCap Cn dn Cl dl N L k
  let F := frontendCap Cf df L k
  let P := preparedCap Cp dp Cn dn Cl dl Cf df N L k
  let A := 12*P+4*N+6
  let T := A+S+2
  let W := S+F+P+4*N+6
  let V := C*(30*(W+1))^e
  have hbase : A+T+n+t+d+J+1 ≤ 30*(W+1) := by
    dsimp only [A,T,W,S] at *
    omega
  have hpow : C*(A+T+n+t+d+J+1)^e ≤ V :=
    Nat.mul_le_mul_left C (Nat.pow_le_pow_left hbase e)
  obtain ⟨hc,_hnodes,hs⟩ := hstream n t d J A T
  have hcompact : QueryHeadBudgets.compact A ≤ V := hc.trans hpow
  have hspace : QueryStreamCorrect.space n t d J A T ≤ V := hs.trans hpow
  have hprefix := setup_prefix_bound_le q Cp dp Cn dn Cl dl Cf df N L k f B hf
    (hqn.trans_le hn)
  have hlocal : 12*P+4*N+6 ≤ envelope C e W := by
    unfold envelope
    dsimp only [W,V]
    omega
  have hfirst : S+F ≤ envelope C e W := by
    unfold envelope
    dsimp only [W]
    omega
  have hvalue : V ≤ envelope C e W := by
    unfold envelope
    simp only [Nat.mul_assoc]
    change V ≤ 1000*(W+1)+1000*V
    omega
  have hnW : n ≤ W := by dsimp only [W]; omega
  have hlinear : 1000*(W+1) ≤ envelope C e W := Nat.le_add_right _ _
  have hrefresh : 20*(n+2) ≤ envelope C e W :=
    (by omega : 20*(n+2) ≤ 1000*(W+1)).trans hlinear
  have hcounter : 40*(h+1) ≤ envelope C e W :=
    (by omega : 40*(h+1) ≤ 1000*(W+1)).trans hlinear
  have hloop : HighQueryCorrect.loopSpace n h t d J A T ≤ envelope C e W :=
    max_le (max_le (max_le (hcompact.trans hvalue) (hspace.trans hvalue))
      hrefresh) hcounter
  have hsuffix : 931*QueryHeadBudgets.compact A+54 ≤ envelope C e W := by
    unfold envelope
    simp only [Nat.mul_assoc]
    change _ ≤ 1000*(W+1)+1000*V
    omega
  change HighQueryCorrect.space q S F (S+f) B (Cp*(S+f+1)^dp)
    (HighQueryCorrect.loopSpace n h t d J A T) (QueryHeadBudgets.compact A) ≤
      max (envelope C e W) B
  unfold HighQueryCorrect.space
  have hp : HighQuerySetup.prefixBound q (S+f) (Cp*(S+f+1)^dp) B ≤
      max (envelope C e W) B := hprefix.trans (max_le_max_right B hlocal)
  exact max_le (hfirst.trans (Nat.le_max_left _ _))
    (max_le (max_le hp (hloop.trans (Nat.le_max_left _ _)))
      (hsuffix.trans (Nat.le_max_left _ _)))

/-- Coefficients and degree are fixed before the query, mark, source state,
node, signature or head assignment. This substitutes the genuine common
leaf bound directly; the retained hidden frame never enters the polynomial. -/
theorem polynomial (Cp dp Cn dn Cl dl Cf df C0 d0 k : ℕ) :
    ∃ C e : ℕ, ∀ (N L : ℕ) (q : LeafQueryFrontend.Query) (n h t d J f B : ℕ),
      L ≤ C0*(N+1)^d0 → BinaryArithmetic.toNat q.ambient = n → n ≤ N → h ≤ n →
      t ≤ sourceCap Cn dn Cl dl N L k →
      d ≤ sourceCap Cn dn Cl dl N L k →
      J ≤ sourceCap Cn dn Cl dl N L k → f ≤ frontendCap Cf df L k →
      querySpace q Cp dp Cn dn Cl dl Cf df N L k n h t d J f B ≤
        max (C*(N+1)^e) B := by
  obtain ⟨Cs,es,hspace⟩ := envelope_bound
  obtain ⟨Cw,ew,hwords⟩ := cap_polynomial Cp dp Cn dn Cl dl Cf df C0 d0 k
  have hw : Ordinary (fun N => Cw*(N+1)^ew) :=
    ordinary_mul (ordinary_const Cw)
      (ordinary_pow (ordinary_add ordinary_id (ordinary_const 1)) ew)
  have hp : Ordinary (fun N => envelope Cs es (Cw*(N+1)^ew)) :=
    ordinary_add (ordinary_mul (ordinary_const 1000) (ordinary_add hw (ordinary_const 1)))
      (ordinary_mul (ordinary_const (1000*Cs))
        (ordinary_pow (ordinary_mul (ordinary_const 30) (ordinary_add hw (ordinary_const 1))) es))
  obtain ⟨C,e,hbound⟩ := hp
  refine ⟨C,e,?_⟩
  intro N L q n h t d J f B hL hqn hn hh ht hd hJ hf
  have h := hspace Cp dp Cn dn Cl dl Cf df N L k q n h t d J f B hqn hn hh ht hd hJ hf
  exact h.trans (max_le_max_right B
    ((envelope_mono Cs es _ _ (hwords N L hL)).trans (hbound N)))

/-- The bounded shadow query has no suspended frame, so its complete
source-prefix bound is this fixed polynomial in the true encoded input. -/
theorem shadow_polynomial (Cp dp Cn dn Cl dl Cf df C0 d0 k : ℕ) :
    ∃ C e : ℕ, ∀ (N L : ℕ) (q : LeafQueryFrontend.Query) (n h t d J f : ℕ),
      L ≤ C0*(N+1)^d0 → BinaryArithmetic.toNat q.ambient = n → n ≤ N → h ≤ n →
      t ≤ sourceCap Cn dn Cl dl N L k →
      d ≤ sourceCap Cn dn Cl dl N L k →
      J ≤ sourceCap Cn dn Cl dl N L k → f ≤ frontendCap Cf df L k →
      querySpace q Cp dp Cn dn Cl dl Cf df N L k n h t d J f 0 ≤ C*(N+1)^e := by
  obtain ⟨C,e,h⟩ := polynomial Cp dp Cn dn Cl dl Cf df C0 d0 k
  refine ⟨C,e,?_⟩
  intro N L q n hsize t d J f hL hqn hn hh ht hd hJ hf
  simpa only [Nat.max_zero] using h N L q n hsize t d J f 0 hL hqn hn hh ht hd hJ hf

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeQuerySpaceBounds
