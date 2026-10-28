import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssemblyLowBounds
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssemblyOutputBounds

namespace OAI.Algorithms

/-! The completed incidence slice has polynomial work and storage, including
all original-variable entries and their raw sparse payloads. -/
namespace SubexponentialSAT.SqrtLog.PerturbationAssembly
attribute [local simp] Fin.coe_ofNat_eq_mod
open SubexponentialSAT DensePolynomialProgram
open SubexponentialSAT.SubexpSymbolicCost SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

theorem nativeLiteralValue_length (t : ℕ) {d : ℕ} (a : RingModel.Data d)
    (M : SubexpPreparedQuartic.Modulus 3 t) (cache : RingProgram.ScalarCache 3 t)
    (J N : ℕ) (theta : Coeff (baseWidth 3 t) d)
    (rows : List (Fixed.Array (baseWidth 3 t) d N × Bool)) (s : OuterStore) (j : ℕ)
    (hz : (s 547).length=d*baseWidth 3 t) (ho : (s 548).length=d*baseWidth 3 t) :
    (nativeLiteralValue t a M cache J N theta rows s j).length ≤
      incidenceBitsBound rows.length J (d*baseWidth 3 t) := by
  unfold nativeLiteralValue
  split
  · have hk : (originKey rows.length).length=rows.length+2 := by
      simp [originKey,PerturbationEmitProgram.keyBits,PerturbationProgram.Key.bits]
    cases hbit:(s 575).getD j false <;>
      simp [hk,hz,ho,incidenceBitsBound] <;> omega
  · simpa using lowOutput_length t a M cache J N theta rows []

def literalWorkPolynomial (n N J t d E H Ksource : ℕ) : ℕ :=
  let W := d*baseWidth 3 t
  7*n+(10*n+9*H+18+(10*n+42*n+29*W+109)+Ksource+
    lowWorkPolynomial n N J t d E+1)+22*(n+1)+19*incidenceBitsBound n J W+
    2*(n*(2*(N*W)+2)+1)+54

theorem literalBudget_polynomial (t : ℕ) {d : ℕ} (a : RingModel.Data d)
    (M : SubexpPreparedQuartic.Modulus 3 t) (cache : RingProgram.ScalarCache 3 t)
    (J N : ℕ) (theta : Coeff (baseWidth 3 t) d)
    (rows : List (Fixed.Array (baseWidth 3 t) d N × Bool)) (s : OuterStore) (j Ksource : ℕ)
    (hj : j ≤ rows.length)
    (hinput : LowInput t a M cache J N theta rows
      (projectInner (literalSourceState s j (sourceWords rows)))) :
    literalBudget t a M cache J N theta rows s j Ksource ≤
      literalWorkPolynomial rows.length N J t d
        ((s 532).length+(s 533).length+(s 583).length) (s 574).length Ksource := by
  have hz : (s 547).length=d*baseWidth 3 t := by
    simpa [literalSourceState,projectInner,Function.comp_def,innerPort] using congrArg List.length hinput.zeroWord
  have ho : (s 548).length=d*baseWidth 3 t := by
    simpa [literalSourceState,projectInner,Function.comp_def,innerPort] using congrArg List.length hinput.oneWord
  have hp := nativeLiteralValue_length t a M cache J N theta rows s j hz ho
  have hl : lowBudget (projectInner (literalSourceState s j (sourceWords rows)))
      rows.length N J t d ≤ lowWorkPolynomial rows.length N J t d
        ((s 532).length+(s 533).length+(s 583).length) := by
    convert hinput.budget_bound using 1 ;
      simp [projectInner,literalSourceState,innerPort]
  unfold literalBudget nativePayloadBudget literalWorkPolynomial
  rw [sourceWords_length]
  dsimp only
  omega

/-- A uniform per-entry bound costs at most n times that bound in the finite
sum used by the actual counted table loop. -/
theorem factorBodyBudget_bound (t : ℕ) {d : ℕ} (a : RingModel.Data d)
    (M : SubexpPreparedQuartic.Modulus 3 t) (cache : RingProgram.ScalarCache 3 t)
    (J N : ℕ) (theta : Coeff (baseWidth 3 t) d)
    (rows : FactorRows t N (d:=d)) (s : OuterStore) (n Ksource : ℕ)
    (hlen : ∀ j,j < n → (rows j).length=n)
    (hinput : ∀ j,j < n → LowInput t a M cache J N theta (rows j)
      (projectInner (literalSourceState s j (sourceWords (rows j))))) :
    factorBodyBudget t a M cache J N theta rows s n Ksource ≤
      n*literalWorkPolynomial n N J t d
        ((s 532).length+(s 533).length+(s 583).length) (s 574).length Ksource := by
  unfold factorBodyBudget
  calc
    _ ≤ ∑ _j ∈ Finset.range n,literalWorkPolynomial n N J t d
        ((s 532).length+(s 533).length+(s 583).length) (s 574).length Ksource := by
      apply Finset.sum_le_sum
      intro j hj
      have hj' := Finset.mem_range.mp hj
      have h := literalBudget_polynomial t a M cache J N theta (rows j) s j Ksource
        (by rw [hlen j hj']; omega) (hinput j hj')
      simpa only [hlen j hj'] using h
    _ = _ := by simp

/-- Exact framing costs for an arbitrary bounded payload family. -/
theorem tableResult_length_bound (payload : ℕ → List Bool) (L n : ℕ)
    (hp : ∀ j,j < n → (payload j).length ≤ L) (acc : List Bool) :
    (tableResult payload n acc).length ≤ acc.length+n*(2*n+2*L+4) := by
  induction n generalizing acc with
  | zero => simp [tableResult]
  | succ n ih =>
      have h := ih (fun j hj=>hp j (by omega)) (tableRecord payload n++acc)
      have hn := hp n (by omega)
      simp only [tableResult,List.length_append,tableRecord,Encoding.length_frame,
        Encoding.encodeNat,List.length_append,List.length_replicate,List.length_singleton] at h ⊢
      nlinarith

end SubexponentialSAT.SqrtLog.PerturbationAssembly

end OAI.Algorithms
