import OAI.AlgebraicGeometry.SheafCohomology.Projective.HilbertSyzygyM
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Finite.GradedPolynomialModules

/-! # Graded Syzygy Dimension -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.GradedSyzygyDimension

noncomputable section

/-! The constructed homogeneous syzygies terminate in a projective polynomial module. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.CategoryTheory.Limits
open OAI.AlgebraicGeometry.HilbertScheme.Presentations.Finite.GradedPolynomialModules.GradedModules
universe u
variable {R : Type u} [CommRing R] {σ : Type}

def gradedModuleObject (D : HilbertScheme.Presentations.Finite.GradedPolynomialModules.GradedModules.FiniteGradedPolynomialModule σ R) : ModuleCat (MvPolynomial σ R) :=
  ModuleCat.of (MvPolynomial σ R) D.Carrier

theorem gradedFreeModule_projective (D : HilbertScheme.Presentations.Finite.GradedPolynomialModules.GradedModules.FiniteGradedPolynomialModule σ R) :
    Projective (gradedModuleObject D.freeModule) := by
  let : Module.Free (MvPolynomial σ R) D.freeModule.Carrier := by
    dsimp only [HilbertScheme.Presentations.Finite.GradedPolynomialModules.GradedModules.FiniteGradedPolynomialModule.freeModule, HilbertScheme.Presentations.Graded.Free.GradedModules.HomogeneousFreeCover.FreeModule]
    infer_instance
  exact ModuleCat.projective_of_free
    (Module.Free.chooseBasis (MvPolynomial σ R) D.freeModule.Carrier)

variable [IsNoetherianRing R] [Finite σ]

def gradedCoverShortComplex (D : HilbertScheme.Presentations.Finite.GradedPolynomialModules.GradedModules.FiniteGradedPolynomialModule σ R) :
    ShortComplex (ModuleCat (MvPolynomial σ R)) :=
  ModuleCat.shortComplexOfCompEqZero D.kernelInclusion D.projection
    (by ext x; exact x.property)

theorem gradedCoverShortComplex_shortExact (D : HilbertScheme.Presentations.Finite.GradedPolynomialModules.GradedModules.FiniteGradedPolynomialModule σ R) :
    (gradedCoverShortComplex D).ShortExact :=
  ModuleCat.shortComplex_shortExact _ D.cover_exact D.kernelInclusion_injective D.projection_surjective

theorem gradedSyzygy_hasProjectiveDimensionLE (D : HilbertScheme.Presentations.Finite.GradedPolynomialModules.GradedModules.FiniteGradedPolynomialModule σ R) (n : ℕ)
    [HasProjectiveDimensionLE (gradedModuleObject D) (n + 1)] :
    HasProjectiveDimensionLE (gradedModuleObject D.syzygy) n := by
  have h := (inferInstance : HasProjectiveDimensionLE (gradedModuleObject D) (n + 1))
  exact ((gradedCoverShortComplex_shortExact D).hasProjectiveDimensionLT_X₃_iff n
    (gradedFreeModule_projective D)).mp h

def iteratedGradedSyzygy (D : HilbertScheme.Presentations.Finite.GradedPolynomialModules.GradedModules.FiniteGradedPolynomialModule σ R) :
    ℕ → HilbertScheme.Presentations.Finite.GradedPolynomialModules.GradedModules.FiniteGradedPolynomialModule σ R
  | 0 => D
  | n + 1 => iteratedGradedSyzygy D.syzygy n

theorem iteratedGradedSyzygy_hasProjectiveDimensionLE
    (D : HilbertScheme.Presentations.Finite.GradedPolynomialModules.GradedModules.FiniteGradedPolynomialModule σ R) (k n : ℕ)
    [HasProjectiveDimensionLE (gradedModuleObject D) (n + k)] :
    HasProjectiveDimensionLE (gradedModuleObject (GradedSyzygyDimension.iteratedGradedSyzygy D k)) n := by
  induction k generalizing D with
  | zero => simpa only [Nat.add_zero, GradedSyzygyDimension.iteratedGradedSyzygy] using
      (inferInstance : HasProjectiveDimensionLE (gradedModuleObject D) (n + 0))
  | succ k ih =>
      have : HasProjectiveDimensionLE (gradedModuleObject D.syzygy) (n + k) :=
        gradedSyzygy_hasProjectiveDimensionLE D (n + k)
      exact ih D.syzygy

theorem iteratedGradedSyzygy_projective_of_field {K : Type u} [Field K]
    (r : ℕ) (D : HilbertScheme.Presentations.Finite.GradedPolynomialModules.GradedModules.FiniteGradedPolynomialModule (Fin r) K) :
    Projective (gradedModuleObject (GradedSyzygyDimension.iteratedGradedSyzygy D r)) := by
  have : HasProjectiveDimensionLE (gradedModuleObject D) (0 + r) := by
    simpa only [Nat.zero_add] using
      HilbertSyzygyM.HilbertSyzygy.hasProjectiveDimensionLE_of_field K r (gradedModuleObject D)
  have := iteratedGradedSyzygy_hasProjectiveDimensionLE D r 0
  exact (projective_iff_hasProjectiveDimensionLE_zero _).mpr this

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.GradedSyzygyDimension
