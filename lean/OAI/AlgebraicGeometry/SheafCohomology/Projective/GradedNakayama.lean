import OAI.AlgebraicGeometry.SheafCohomology.Projective.GradedPolynomialConstantComponent
import Mathlib.RingTheory.Finiteness.Nakayama

/-! # Graded Nakayama -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.GradedNakayama

noncomputable section

/-! Nakayama's lemma for finite graded polynomial modules at the augmentation ideal. -/

open DirectSum _root_.MvPolynomial
universe u
variable {R : Type u} [CommRing R] {σ : Type} [Fintype σ]

def polynomialAugmentationIdeal : Ideal (MvPolynomial σ R) :=
  RingHom.ker (constantCoeff : MvPolynomial σ R →+* R)

theorem gradedPolynomial_nakayama
    {M : Type u} [AddCommGroup M] [Module R M] [Module (MvPolynomial σ R) M]
    [IsScalarTower R (MvPolynomial σ R) M] [Module.Finite (MvPolynomial σ R) M]
    (ℳ : ℤ → Submodule R M) [Decomposition ℳ]
    [SetLike.GradedSMul (HilbertScheme.Presentations.WeightedFreeModules.GradedModules.polynomialIntegerGrading (σ := σ) R) ℳ]
    (h : (⊤ : Submodule (MvPolynomial σ R) M) ≤ polynomialAugmentationIdeal (R := R) (σ := σ) • ⊤) :
    Subsingleton M := by
  obtain ⟨p, hp, hzero⟩ := Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul
    (polynomialAugmentationIdeal (R := R) (σ := σ)) (⊤ : Submodule (MvPolynomial σ R) M) Module.Finite.fg_top h
  have hc : constantCoeff p = 1 := by
    change constantCoeff (p - 1) = 0 at hp
    rw [map_sub, map_one] at hp
    exact sub_eq_zero.mp hp
  have hall (x : M) : x = 0 := by
    induction x using Decomposition.inductionOn ℳ with
    | zero => rfl
    | add x y hx hy => rw [hx, hy, add_zero]
    | homogeneous x =>
        have hx := GradedPolynomialConstantComponent.homogeneous_smul_constant_component ℳ x.property p
        rw [hzero x.val (by trivial), hc, one_smul] at hx
        simpa only [decompose_zero, DFinsupp.zero_apply, Submodule.coe_zero] using hx.symm
  exact ⟨fun x y => (hall x).trans (hall y).symm⟩

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.GradedNakayama
