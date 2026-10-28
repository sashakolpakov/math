import OAI.AlgebraicGeometry.HodgeConjecture.CMReduction.EvenAppend
import OAI.AlgebraicGeometry.HodgeConjecture.CMReduction.CupPermutation
import OAI.AlgebraicGeometry.HodgeConjecture.CMReduction.CanonicalExterior
import OAI.AlgebraicGeometry.HodgeConjecture.CMReduction.AmplePowers
import Mathlib.Logic.Equiv.Sum

/-! # Pair Products -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMReduction.PairProducts.CM.Construction

noncomputable section

/-! Arbitrarily many algebraic opposite pairs give an algebraic endpoint
tensor. A concrete index equivalence relates pair order to endpoint order. -/

open _root_.CategoryTheory

def pairedIndexEquiv : (n : ℕ) → Fin (n + n) ≃ Fin n ⊕ Fin n
  | 0 => Equiv.equivOfIsEmpty (Fin 0) (Fin 0 ⊕ Fin 0)
  | n + 1 =>
    (finCongr (add_add_add_comm n n 1 1).symm).trans
      (finSumFinEquiv.symm.trans
        ((Equiv.sumCongr (pairedIndexEquiv n)
          (finSumFinEquiv : Fin 1 ⊕ Fin 1 ≃ Fin (1 + 1)).symm).trans
          ((Equiv.sumSumSumComm (Fin n) (Fin n) (Fin 1) (Fin 1)).trans
            (Equiv.sumCongr finSumFinEquiv finSumFinEquiv))))

def pairedTuple {α : Type*} (n : ℕ) (x y : Fin n → α) : Fin (n + n) → α :=
  Sum.elim x y ∘ Construction.pairedIndexEquiv n

theorem pairedTuple_succ {α : Type*} (n : ℕ) (x y : Fin (n + 1) → α) :
    pairedTuple (n + 1) x y = EvenAppend.CM.Construction.evenAppend n 1
      (pairedTuple n (Fin.init x) (Fin.init y)) ![x (Fin.last n), y (Fin.last n)] := by
  let e : Fin ((n + 1) + (n + 1)) ≃ Fin (n + n) ⊕ Fin (1 + 1) :=
    (finCongr (add_add_add_comm n n 1 1).symm).trans finSumFinEquiv.symm
  funext i
  obtain ⟨j, rfl⟩ := e.symm.surjective i
  rcases j with j | j
  · cases h : Construction.pairedIndexEquiv n j <;>
      simp [pairedTuple, Construction.pairedIndexEquiv, EvenAppend.CM.Construction.evenAppend, e, h, Fin.init] <;> rfl
  · fin_cases j
    · simp [pairedTuple, Construction.pairedIndexEquiv, EvenAppend.CM.Construction.evenAppend, e,
        show (finSumFinEquiv : Fin 1 ⊕ Fin 1 ≃ Fin 2).symm 0 = Sum.inl 0 from rfl]
      rfl
    · simp [pairedTuple, Construction.pairedIndexEquiv, EvenAppend.CM.Construction.evenAppend, e,
        show (finSumFinEquiv : Fin 1 ⊕ Fin 1 ≃ Fin 2).symm 1 = Sum.inr 0 from rfl]
      rfl

theorem pairedTuple_reorder {α : Type*} (n : ℕ) (x y : Fin n → α) :
    pairedTuple n x y ∘ (finSumFinEquiv.symm.trans (Construction.pairedIndexEquiv n).symm) = Fin.append x y := by
  funext i
  simp only [pairedTuple, Function.comp_apply, Equiv.trans_apply, Equiv.apply_symm_apply]
  obtain ⟨j, rfl⟩ := (finSumFinEquiv : Fin n ⊕ Fin n ≃ Fin (n + n)).surjective i
  rw [Equiv.symm_apply_apply]
  cases j with
  | inl j => exact (Fin.append_left x y j).symm
  | inr j => exact (Fin.append_right x y j).symm

theorem h1Cup_pairedTuple_algebraic (h_LineBundleCycles : CycleOperations.CM.Construction.LineBundleCyclesInput) (h_ThomClass : CycleOperations.CM.Construction.ExteriorInput)
    (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (p : ℕ) (x y : Fin p → A.variety.complexCohomology 1)
    (hpair : ∀ i, AlgebraicTopology.Products.CupCohomology.singularCohomologyCup (R := ℂ) (Betti.Scheme.schemePointSpace A.toOver) 1 1 (x i) (y i) ∈
      A.variety.complexGeometricAlgebraicClasses 1) :
    IteratedCup.CM.Construction.h1Cup ℂ (Betti.Scheme.schemePointSpace A.toOver) (p + p) (pairedTuple p x y) ∈
      A.variety.complexGeometricAlgebraicClasses p := by
  induction p with
  | zero =>
    have hu := Descent.CM.Construction.rational_algebraic_complex_inclusion A.variety 0 _ (AmplePowers.CM.Construction.rational_unit_algebraic A.variety)
    change AlgebraicTopology.Cohomology.Singular.RationalComplex.rationalToComplexCohomology (Betti.Scheme.schemePointSpace A.toOver) 0
      (AlgebraicTopology.Products.CupCohomologyAlgebra.singularCohomologyCupUnit (R := ℚ) (Betti.Scheme.schemePointSpace A.toOver)) ∈ _ at hu
    rw [ComplexMultiplication.HodgeComparison.RationalCupUnit.CM.Construction.rationalToComplexCohomology_unit] at hu
    exact hu
  | succ p ih =>
    rw [pairedTuple_succ]
    apply EvenAppend.CM.Construction.h1Cup_evenAppend_algebraic h_LineBundleCycles h_ThomClass A p 1
    · exact ih (Fin.init x) (Fin.init y) (fun i => hpair i.castSucc)
    · rw [CupAppend.CM.Construction.h1Cup_two]
      exact hpair (Fin.last p)

theorem h1Cup_of_algebraic_pairs (hexterior : ComplexMultiplication.KnownExteriorCohomology.CM.KnownResults.AbelianExteriorCohomology)
    (h_LineBundleCycles : CycleOperations.CM.Construction.LineBundleCyclesInput) (h_ThomClass : CycleOperations.CM.Construction.ExteriorInput)
    (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (p : ℕ) (x y : Fin p → A.variety.complexCohomology 1)
    (hpair : ∀ i, AlgebraicTopology.Products.CupCohomology.singularCohomologyCup (R := ℂ) (Betti.Scheme.schemePointSpace A.toOver) 1 1 (x i) (y i) ∈
      A.variety.complexGeometricAlgebraicClasses 1) :
    IteratedCup.CM.Construction.h1Cup ℂ (Betti.Scheme.schemePointSpace A.toOver) (p + p) (Fin.append x y) ∈
      A.variety.complexGeometricAlgebraicClasses p := by
  have h := CupPermutation.CM.Construction.h1Cup_perm_mem (CanonicalExterior.CM.Construction.canonicalExterior hexterior A) p (pairedTuple p x y)
    (finSumFinEquiv.symm.trans (Construction.pairedIndexEquiv p).symm)
    (h1Cup_pairedTuple_algebraic h_LineBundleCycles h_ThomClass A p x y hpair)
  rwa [pairedTuple_reorder] at h

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMReduction.PairProducts.CM.Construction
