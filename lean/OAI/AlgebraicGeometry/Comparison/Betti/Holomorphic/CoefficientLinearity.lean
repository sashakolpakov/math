import OAI.AlgebraicGeometry.Comparison.Betti.Smooth.CoefficientLinearity
import OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.Factorization
import OAI.AlgebraicGeometry.Comparison.Betti.ManifoldHolomorphicModules
import OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.RegularSections

/-! # Coefficient Linearity -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.CoefficientLinearity

noncomputable section

/-! The preserved holomorphic comparison is linear over actual regular-section evaluation. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.Manifold ContDiff

namespace Smooth

variable {E M A : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
  [IsScalarTower ℝ ℂ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [IsManifold 𝓘(ℂ, E) ∞ M]
  [CommRing A] [Algebra ℂ A]
  (φ : A →ₐ[ℂ] C(M, ℂ))
  (hφ : ∀ a, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) ∞ (φ a))
  (hc : ∀ a, ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, ℂ) ∞ (φ a))

theorem holomorphicFormMap_coefficient_smul (n : ℕ) (c : A) (a : Algebraic.Forms.Form A n) :
    Factorization.Smooth.holomorphicFormMap φ hφ hc n (c • a) =
      FunctionMultiplication.multiplyByHolomorphicFunction
        (⟨φ c, hc c⟩ : C^∞⟮𝓘(ℂ, E), M; 𝓘(ℂ), ℂ⟯) n (Factorization.Smooth.holomorphicFormMap φ hφ hc n a) := by
  apply HolomorphicPullback.inclusion_injective n
  exact Betti.Smooth.CoefficientLinearity.smoothFormMap_coefficient_smul φ hφ n c a

end Smooth

attribute [local instance] Algebraic.Sheaves.sectionAlgebra

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X.left] [Smooth X.hom]

theorem openHolomorphicCochainMap_coefficient_smul (U : X.left.Opens) (n : ℕ)
    (c : Γ(X.left, U)) (a : Algebraic.Forms.Form Γ(X.left, U) n) :
    (Algebraic.Holomorphic.openHolomorphicCochainMap X U).f n (c • a) =
      FunctionMultiplication.multiplyByHolomorphicFunction (RegularSections.regularHolomorphicSectionMap X U c) n
        ((Algebraic.Holomorphic.openHolomorphicCochainMap X U).f n a) :=
  CoefficientLinearity.Smooth.holomorphicFormMap_coefficient_smul (Open.AffineIsoEvaluation.sectionEvaluationOn X U)
    (Open.SmoothEvaluation.sectionEvaluationOn_smooth X U) (HodgeConjecture.CMExtraction.HolomorphicSections.Kaehler.sectionEvaluationOn_holomorphic X U)
    n c a

def exteriorToHolomorphicFormMap (U : X.left.Opens) (n : ℕ) :
    (⋀[Γ(X.left, U)]^n Ω[Γ(X.left, U)⁄ℂ]) →ₛₗ[(RegularSections.regularHolomorphicSectionMap X U).toRingHom]
      DeRhamComplex.forms (RegularSmoothness.NativeModel X) (Open.AffineIsoEvaluation.analyticOpen X U) n where
  toFun a := (Algebraic.Holomorphic.openHolomorphicCochainMap X U).f n
    ((Algebraic.CoefficientAction.exteriorFormsCoefficientEquiv Γ(X.left, U) n).symm a)
  map_add' a b := by
    rw [map_add]
    exact ((Algebraic.Holomorphic.openHolomorphicCochainMap X U).f n).hom.map_add _ _
  map_smul' c a := by
    rw [map_smul]
    exact openHolomorphicCochainMap_coefficient_smul X U n c _

theorem exteriorToHolomorphicFormMap_normalization (U : X.left.Opens) (n : ℕ)
    (a : Algebraic.Forms.Form Γ(X.left, U) n) :
    exteriorToHolomorphicFormMap X U n (Exterior.Forms.exteriorFormsEquiv Γ(X.left, U) n a) =
      (Algebraic.Holomorphic.openHolomorphicCochainMap X U).f n a := by
  change (Algebraic.Holomorphic.openHolomorphicCochainMap X U).f n
    ((Exterior.Forms.exteriorFormsEquiv Γ(X.left, U) n).symm
      (Exterior.Forms.exteriorFormsEquiv Γ(X.left, U) n a)) = _
  rw [LinearEquiv.symm_apply_apply]

end

end OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.CoefficientLinearity
