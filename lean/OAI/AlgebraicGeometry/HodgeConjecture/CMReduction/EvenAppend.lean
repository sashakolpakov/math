import OAI.AlgebraicGeometry.HodgeConjecture.CMReduction.CupAppend
import OAI.AlgebraicGeometry.HodgeConjecture.CMReduction.ComplexOperations

/-! # Even Append -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMReduction.EvenAppend.CM.Construction

noncomputable section

/-! Concatenating even-length H1 blocks agrees with the actual even cup,
including its explicit natural-number degree transport. -/

open _root_.CategoryTheory

def evenAppend {α : Type*} (p q : ℕ)
    (u : Fin (p + p) → α) (v : Fin (q + q) → α) : Fin ((p + q) + (p + q)) → α :=
  Fin.append u v ∘ Fin.cast (add_add_add_comm p p q q).symm

theorem h1Cup_cast {R : Type} [CommRing R] (X : TopCat.{0})
    {n m : ℕ} (h : n = m) (v : Fin n → AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of R R) X 1) :
    IteratedCup.CM.Construction.h1Cup R X m (v ∘ Fin.cast h.symm) =
      AlgebraicTopology.Products.CupCohomologyAlgebra.cohomologyCast (TopCat.toSSet.obj X) (ModuleCat.of R R) h (IteratedCup.CM.Construction.h1Cup R X n v) := by
  subst m
  rfl

theorem h1Cup_evenAppend {R : Type} [CommRing R] (X : TopCat.{0}) (p q : ℕ)
    (u : Fin (p + p) → AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of R R) X 1)
    (v : Fin (q + q) → AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of R R) X 1) :
    IteratedCup.CM.Construction.h1Cup R X ((p + q) + (p + q)) (evenAppend p q u v) =
      ComplexOperations.CM.Construction.evenCup R X p q (IteratedCup.CM.Construction.h1Cup R X (p + p) u) (IteratedCup.CM.Construction.h1Cup R X (q + q) v) := by
  unfold evenAppend
  rw [h1Cup_cast X (add_add_add_comm p p q q), CupAppend.CM.Construction.h1Cup_append X (p + p) (q + q)]
  rfl

theorem h1Cup_evenAppend_algebraic (h_LineBundleCycles : CycleOperations.CM.Construction.LineBundleCyclesInput) (h_ThomClass : CycleOperations.CM.Construction.ExteriorInput)
    (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (p q : ℕ)
    (u : Fin (p + p) → A.variety.complexCohomology 1)
    (v : Fin (q + q) → A.variety.complexCohomology 1)
    (hu : IteratedCup.CM.Construction.h1Cup ℂ (Betti.Scheme.schemePointSpace A.toOver) (p + p) u ∈ A.variety.complexGeometricAlgebraicClasses p)
    (hv : IteratedCup.CM.Construction.h1Cup ℂ (Betti.Scheme.schemePointSpace A.toOver) (q + q) v ∈ A.variety.complexGeometricAlgebraicClasses q) :
    IteratedCup.CM.Construction.h1Cup ℂ (Betti.Scheme.schemePointSpace A.toOver) ((p + q) + (p + q)) (evenAppend p q u v) ∈
      A.variety.complexGeometricAlgebraicClasses (p + q) := by
  rw [h1Cup_evenAppend]
  exact ComplexOperations.CM.Construction.complex_cup_algebraic h_LineBundleCycles h_ThomClass A.variety p q _ _ hu hv

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMReduction.EvenAppend.CM.Construction
