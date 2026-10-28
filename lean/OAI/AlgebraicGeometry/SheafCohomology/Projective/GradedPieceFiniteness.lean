import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Finite.GradedPolynomialModules
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.IntegerPolynomialGrading
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Graded.Exactness
import Mathlib.LinearAlgebra.Dimension.Finite

/-! # Graded Piece Finiteness -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.GradedPieceFiniteness

noncomputable section

/-! Finite homogeneous pieces of finite graded polynomial modules. -/

open _root_.Module _root_.MvPolynomial DirectSum
universe u v w

variable {σ : Type u} [Fintype σ] (R : Type v) [CommRing R]

theorem polynomialIntegerGrading_eq_bot_of_neg (d : ℤ) (hd : d < 0) :
    HilbertScheme.Presentations.WeightedFreeModules.GradedModules.polynomialIntegerGrading (σ := σ) R d = ⊥ := by
  apply bot_unique
  intro p hp
  change p = 0
  apply MvPolynomial.ext
  intro a
  rw [AddMonoidAlgebra.coeff_zero]
  by_contra ha
  have h := hp ha
  rw [HilbertScheme.Presentations.IntegerPolynomialGrading.GradedModules.integerWeight_eq_degree] at h
  omega

theorem polynomialIntegerGrading_finite (d : ℤ) :
    Module.Finite R (HilbertScheme.Presentations.WeightedFreeModules.GradedModules.polynomialIntegerGrading (σ := σ) R d) := by
  by_cases hd : 0 ≤ d
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hd
    rw [HilbertScheme.Presentations.IntegerPolynomialGrading.GradedModules.polynomialIntegerGrading_nat]
    exact Module.Finite.of_fg (MvPolynomial.homogeneousSubmodule_fg σ R n)
  · rw [polynomialIntegerGrading_eq_bot_of_neg R d (by omega)]
    infer_instance

def weightedFreePieceToPi {ι : Type w} (w : ι → ℤ) (d : ℤ) :
    HilbertScheme.Presentations.WeightedFreeModules.GradedModules.weightedFreeGrading (σ := σ) R w d →ₗ[R]
      ∀ i, HilbertScheme.Presentations.WeightedFreeModules.GradedModules.polynomialIntegerGrading (σ := σ) R (d - w i) where
  toFun f i := ⟨f.val i, (HilbertScheme.Presentations.WeightedFreeModules.GradedModules.mem_weightedFreeGrading R w d f.val).mp f.property i⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [Fintype σ] in
theorem weightedFreePieceToPi_injective {ι : Type w} (w : ι → ℤ) (d : ℤ) :
    Function.Injective (weightedFreePieceToPi (σ := σ) R w d) := by
  intro f g h
  apply Subtype.ext
  apply Finsupp.ext
  intro i
  exact congrArg (fun x => (x i).val) h

theorem weightedFreeGrading_finite [IsNoetherianRing R]
    {ι : Type w} [Finite ι] (w : ι → ℤ) (d : ℤ) :
    Module.Finite R (HilbertScheme.Presentations.WeightedFreeModules.GradedModules.weightedFreeGrading (σ := σ) R w d) := by
  have (i : ι) : Module.Finite R (HilbertScheme.Presentations.WeightedFreeModules.GradedModules.polynomialIntegerGrading (σ := σ) R (d - w i)) :=
    polynomialIntegerGrading_finite R (d - w i)
  exact Module.Finite.of_injective (weightedFreePieceToPi (σ := σ) R w d)
    (weightedFreePieceToPi_injective R w d)

theorem finiteGradedPolynomialModule_piece_finite [IsNoetherianRing R]
    (D : HilbertScheme.Presentations.Finite.GradedPolynomialModules.GradedModules.FiniteGradedPolynomialModule σ R) (d : ℤ) : Module.Finite R (D.grading d) := by
  have : Module.Finite R (D.freeModule.grading d) :=
    weightedFreeGrading_finite R D.cover.degree d
  exact Module.Finite.of_surjective
    (HilbertScheme.Presentations.Graded.Exactness.GradedModules.degreeMap D.freeModule.grading D.grading (D.projection.restrictScalars R)
      D.projection_homogeneous d)
    (HilbertScheme.Presentations.Graded.Exactness.GradedModules.degreeMap_surjective D.freeModule.grading D.grading (D.projection.restrictScalars R)
      D.projection_homogeneous D.projection_surjective d)

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.GradedPieceFiniteness
