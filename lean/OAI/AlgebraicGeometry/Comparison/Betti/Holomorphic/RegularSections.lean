import OAI.AlgebraicGeometry.Comparison.Betti.Algebraic.Holomorphic
import Mathlib.Geometry.Manifold.Algebra.SmoothFunctions

/-! # Regular Sections -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.RegularSections

noncomputable section

/-! Actual regular-section evaluation as a complex-algebra map into standard holomorphic functions. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

attribute [local instance] Algebraic.Sheaves.sectionAlgebra

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X.left] [Smooth X.hom]

def regularHolomorphicSectionMap (U : X.left.Opens) :
    Γ(X.left, U) →ₐ[ℂ] C^∞⟮𝓘(ℂ, RegularSmoothness.NativeModel X), Open.AffineIsoEvaluation.analyticOpen X U; 𝓘(ℂ), ℂ⟯ where
  toFun s := ⟨Open.AffineIsoEvaluation.sectionEvaluationOn X U s,
    HodgeConjecture.CMExtraction.HolomorphicSections.Kaehler.sectionEvaluationOn_holomorphic X U s⟩
  map_zero' := by
    apply ContMDiffMap.ext
    intro p
    exact congrArg (fun f : C(Open.AffineIsoEvaluation.analyticOpen X U, ℂ) => f p) (map_zero (Open.AffineIsoEvaluation.sectionEvaluationOn X U))
  map_one' := by
    apply ContMDiffMap.ext
    intro p
    exact congrArg (fun f : C(Open.AffineIsoEvaluation.analyticOpen X U, ℂ) => f p) (map_one (Open.AffineIsoEvaluation.sectionEvaluationOn X U))
  map_add' s t := by
    apply ContMDiffMap.ext
    intro p
    exact congrArg (fun f : C(Open.AffineIsoEvaluation.analyticOpen X U, ℂ) => f p) (map_add (Open.AffineIsoEvaluation.sectionEvaluationOn X U) s t)
  map_mul' s t := by
    apply ContMDiffMap.ext
    intro p
    exact congrArg (fun f : C(Open.AffineIsoEvaluation.analyticOpen X U, ℂ) => f p) (map_mul (Open.AffineIsoEvaluation.sectionEvaluationOn X U) s t)
  commutes' c := by
    apply ContMDiffMap.ext
    intro p
    exact congrArg (fun f : C(Open.AffineIsoEvaluation.analyticOpen X U, ℂ) => f p) ((Open.AffineIsoEvaluation.sectionEvaluationOn X U).commutes c)

theorem regularHolomorphicSectionMap_apply (U : X.left.Opens) (s : Γ(X.left, U))
    (p : Open.AffineIsoEvaluation.analyticOpen X U) : regularHolomorphicSectionMap X U s p = Open.AffineIsoEvaluation.sectionEvaluationOn X U s p := rfl

theorem regularHolomorphicSectionMap_restrict {U V : X.left.Opens} (h : V ≤ U)
    (s : Γ(X.left, U)) :
    regularHolomorphicSectionMap X V (X.left.presheaf.map (homOfLE h).op s) =
      (regularHolomorphicSectionMap X U s).comp
        ⟨Opens.inclusion (Open.SmoothForms.analyticOpen_mono X h),
          contMDiff_inclusion (I := 𝓘(ℂ, RegularSmoothness.NativeModel X)) (Open.SmoothForms.analyticOpen_mono X h)⟩ := by
  apply ContMDiffMap.ext
  intro p
  exact Open.AffineIsoEvaluation.sectionEvaluationOn_restrict X h s p

end

end OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.RegularSections
