import OAI.Analysis.DifferentialForms.Manifold.IntrinsicOpenEquivalence
import OAI.Analysis.DifferentialForms.Manifold.OpenEquivalence
import OAI.Analysis.DifferentialForms.Manifold.NormedSpace

/-! # Local Normed Form Equivalence -/

namespace OAI.Analysis.DifferentialForms.Manifold.LocalNormedFormEquivalence

noncomputable section

/-!
# Ambient local manifold forms in normed-space coordinates

On an open subset of a normed space, the ambient local manifold-form model
identifies with the actual open-domain coefficient-form model. The map is
the composition of the two proved intrinsic open-manifold identifications.
-/

open Set _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {U V : Opens E} {n : ℕ}

/-- The normed inclusion chart and intrinsic inclusion have the same actual tangent map. -/
theorem openTangentEquiv_eq_intrinsic (x : U) :
    OpenEquivalence.openTangentEquiv x = (IntrinsicOpenTangent.intrinsicOpenTangentEquiv x).trans
      (NormedSpace.fromTangentSpace (𝕜 := ℝ) (x : E)) := by
  ext v
  rfl

/-- The two inclusion tangent transports cancel to the ambient normed tangent identification. -/
theorem openInclusion_comp_openTangentInverse (x : U) :
    (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (Subtype.val : U → E) x).comp
        (OpenEquivalence.openTangentEquiv x).symm.toContinuousLinearMap =
      (NormedSpace.fromTangentSpace (𝕜 := ℝ) (x : E)).symm.toContinuousLinearMap := by
  ext v
  apply (NormedSpace.fromTangentSpace (𝕜 := ℝ) (x : E)).injective
  calc
    _ = OpenEquivalence.openTangentEquiv x ((OpenEquivalence.openTangentEquiv x).symm v) := by
      exact congrArg (fun linear => linear ((OpenEquivalence.openTangentEquiv x).symm v))
        (openTangentEquiv_eq_intrinsic x).symm
    _ = v := (OpenEquivalence.openTangentEquiv x).apply_symm_apply v
    _ = _ := (NormedSpace.fromTangentSpace (𝕜 := ℝ) (x : E)).apply_symm_apply v |>.symm

/-- Actual ambient local manifold forms are exactly smooth coefficient forms on the open set. -/
def localNormedFormEquiv (U : Opens E) (n : ℕ) :
    Open.SmoothOpenManifoldForm E U n ≃ₗ[ℂ] OpenD.SmoothOpenForm U n :=
  (IntrinsicOpenEquivalence.intrinsicOpenFormEquiv E U n).trans (OpenEquivalence.smoothOpenManifoldEquiv U n).symm

/-- The coordinate coefficients use the canonical ambient tangent equivalence. -/
@[simp]
theorem localNormedFormEquiv_apply (form : Open.SmoothOpenManifoldForm E U n) (x : U) :
    localNormedFormEquiv U n form x = (form x).compContinuousLinearMap
      (NormedSpace.fromTangentSpace (𝕜 := ℝ) (x : E)).symm.toContinuousLinearMap := by
  change ((form x).compContinuousLinearMap
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (Subtype.val : U → E) x)).compContinuousLinearMap
      (OpenEquivalence.openTangentEquiv x).symm.toContinuousLinearMap = _
  ext v
  apply congrArg (form x)
  funext i
  exact congrArg (fun linear => linear (v i)) (openInclusion_comp_openTangentInverse x)

/-- The identification commutes with the actual exterior derivatives. -/
theorem localNormedFormEquiv_d (form : Open.SmoothOpenManifoldForm E U n) :
    OpenD.SmoothOpenForm.d (localNormedFormEquiv U n form) =
      localNormedFormEquiv U (n + 1) (Open.SmoothOpenManifoldForm.d form) := by
  change OpenD.SmoothOpenForm.d ((OpenEquivalence.smoothOpenManifoldEquiv U n).symm
      (IntrinsicOpenEquivalence.intrinsicOpenFormEquiv E U n form)) =
    (OpenEquivalence.smoothOpenManifoldEquiv U (n + 1)).symm
      (IntrinsicOpenEquivalence.intrinsicOpenFormEquiv E U (n + 1) (Open.SmoothOpenManifoldForm.d form))
  rw [← OpenEquivalence.smoothOpenManifoldEquiv_symm_d, IntrinsicOpenEquivalence.intrinsicOpenFormEquiv_d]

/-- Restriction of actual local manifold forms is ordinary restriction of the coefficients. -/
theorem localNormedFormEquiv_restrict (h : U ≤ V) (form : Open.SmoothOpenManifoldForm E V n) :
    localNormedFormEquiv U n (Open.SmoothOpenManifoldForm.restrict h form) =
      OpenD.SmoothOpenForm.restrict h (localNormedFormEquiv V n form) := by
  apply OpenD.SmoothOpenForm.ext
  intro x
  rw [localNormedFormEquiv_apply, OpenD.SmoothOpenForm.restrict_apply,
    localNormedFormEquiv_apply, Open.SmoothOpenManifoldForm.restrict_apply]

/-- On a restricted global manifold form, the coordinates agree with the existing global map. -/
theorem localNormedFormEquiv_onOpen (form : Algebra.SmoothManifoldForm E E n) :
    localNormedFormEquiv U n (Algebra.SmoothManifoldForm.onOpen U form) =
      Basic.SmoothForm.onOpen U form.toNormedSpace := by
  apply OpenD.SmoothOpenForm.ext
  intro x
  rw [localNormedFormEquiv_apply]
  rfl

end

end OAI.Analysis.DifferentialForms.Manifold.LocalNormedFormEquivalence
