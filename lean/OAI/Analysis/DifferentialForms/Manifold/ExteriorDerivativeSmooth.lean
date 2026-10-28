import Mathlib.Analysis.Calculus.DifferentialForm.Basic
import Mathlib.Analysis.Calculus.ContDiff.Comp

/-! # Exterior Derivative Smooth -/

namespace OAI.Analysis.DifferentialForms.Manifold.ExteriorDerivativeSmooth

/-!
# Regularity of the exterior derivative on a normed vector space

These lemmas use mathlib's actual exterior derivative, defined by alternating
the Fréchet derivative. They make the loss of one finite derivative explicit;
in particular the exterior derivative preserves smoothness.
-/

open scoped ContDiff

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {n : ℕ} {r s : WithTop ℕ∞}
  {form : E → E [⋀^Fin n]→L[𝕜] F}

/-- Taking the exterior derivative loses at most one derivative. -/
theorem contDiff_extDeriv_of_add_one_le (hform : ContDiff 𝕜 s form) (hrs : r + 1 ≤ s) :
    ContDiff 𝕜 r (extDeriv form) := by
  change ContDiff 𝕜 r
    ((ContinuousAlternatingMap.alternatizeUncurryFinCLM 𝕜 E F) ∘ fderiv 𝕜 form)
  exact (ContinuousAlternatingMap.alternatizeUncurryFinCLM 𝕜 E F).contDiff.comp
    (hform.fderiv_right hrs)

/-- The exterior derivative of a smooth differential form is smooth. -/
theorem contDiff_extDeriv_infty (hform : ContDiff 𝕜 ∞ form) :
    ContDiff 𝕜 ∞ (extDeriv form) :=
  contDiff_extDeriv_of_add_one_le hform (by simp)

/-- Local regularity of the exterior derivative, with the derivative order explicit. -/
theorem contDiffAt_extDeriv_of_add_one_le {x : E}
    (hform : ContDiffAt 𝕜 s form x) (hrs : r + 1 ≤ s) :
    ContDiffAt 𝕜 r (extDeriv form) x := by
  change ContDiffAt 𝕜 r
    ((ContinuousAlternatingMap.alternatizeUncurryFinCLM 𝕜 E F) ∘ fderiv 𝕜 form) x
  exact (ContinuousAlternatingMap.alternatizeUncurryFinCLM 𝕜 E F).contDiff.contDiffAt.comp x
    (hform.fderiv_right hrs)

/-- Relative exterior differentiation preserves the expected regularity on a
set with unique derivatives. -/
theorem contDiffOn_extDerivWithin_of_add_one_le {U : Set E}
    (hform : ContDiffOn 𝕜 s form U) (hU : UniqueDiffOn 𝕜 U) (hrs : r + 1 ≤ s) :
    ContDiffOn 𝕜 r (fun x => extDerivWithin form U x) U := by
  change ContDiffOn 𝕜 r
    ((ContinuousAlternatingMap.alternatizeUncurryFinCLM 𝕜 E F) ∘ fderivWithin 𝕜 form U) U
  exact (hform.fderivWithin hU hrs).continuousLinearMap_comp
    (ContinuousAlternatingMap.alternatizeUncurryFinCLM 𝕜 E F)

/-- On an open set, the ordinary exterior derivative has the same local
regularity as the relative one. -/
theorem contDiffOn_extDeriv_of_isOpen {U : Set E}
    (hform : ContDiffOn 𝕜 s form U) (hU : IsOpen U) (hrs : r + 1 ≤ s) :
    ContDiffOn 𝕜 r (extDeriv form) U := by
  change ContDiffOn 𝕜 r
    ((ContinuousAlternatingMap.alternatizeUncurryFinCLM 𝕜 E F) ∘ fderiv 𝕜 form) U
  exact (hform.fderiv_of_isOpen hU hrs).continuousLinearMap_comp
    (ContinuousAlternatingMap.alternatizeUncurryFinCLM 𝕜 E F)

end OAI.Analysis.DifferentialForms.Manifold.ExteriorDerivativeSmooth
