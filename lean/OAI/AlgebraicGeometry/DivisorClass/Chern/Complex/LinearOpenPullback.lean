import OAI.AlgebraicGeometry.DivisorClass.Chern.Complex.LinearDolbeaultPullback
import OAI.AlgebraicGeometry.DivisorClass.Chern.Open.DolbeaultPrime
import OAI.Analysis.DifferentialForms.Manifold.OpenPullback

/-! # Linear Open Pullback -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Complex.LinearOpenPullback

noncomputable section

/-! Original open-form pullbacks along complex-linear maps preserve the actual Dolbeault differential and type. -/

open _root_.ContinuousAlternatingMap _root_.TopologicalSpace Set Filter
open scoped ContDiff _root_.Topology

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F]
  {U : Opens E} {V : Opens F} {n p q : ℕ}

def complexLinearOpenPullback (L : E →L[ℂ] F) (hL : MapsTo L (U : Set E) (V : Set F)) :
    Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm V n →ₗ[ℂ] Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm U n :=
  Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.pullback L (L.restrictScalars ℝ).contDiff.contDiffOn hL

theorem complexLinearOpenPullback_apply (L : E →L[ℂ] F)
    (hL : MapsTo L (U : Set E) (V : Set F)) (a : Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm V n) (x : U) :
    complexLinearOpenPullback L hL a x =
      (a ⟨L x, hL x.property⟩).compContinuousLinearMap (L.restrictScalars ℝ) := by
  change Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.pullback L (L.restrictScalars ℝ).contDiff.contDiffOn hL a x = _
  rw [Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.pullback_apply]
  have hd : fderiv ℝ (fun y => L y) (x : E) = L.restrictScalars ℝ :=
    (L.restrictScalars ℝ).hasFDerivAt.fderiv
  exact congrArg (fun D : E →L[ℝ] F => (a ⟨L x, hL x.property⟩).compContinuousLinearMap D) hd

theorem complexLinearOpenPullback_extension (L : E →L[ℂ] F)
    (hL : MapsTo L (U : Set E) (V : Set F)) (a : Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm V n) (x : U) :
    (complexLinearOpenPullback L hL a).extension =ᶠ[𝓝 (x : E)] LinearDolbeaultPullback.rawComplexLinearPullback L a.extension := by
  filter_upwards [U.isOpen.mem_nhds x.property] with y hy
  rw [show (complexLinearOpenPullback L hL a).extension y =
    complexLinearOpenPullback L hL a ⟨y, hy⟩ from Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.extension_apply _ ⟨y, hy⟩,
    complexLinearOpenPullback_apply]
  unfold LinearDolbeaultPullback.rawComplexLinearPullback
  rw [show a.extension (L y) = a ⟨L y, hL hy⟩ from a.extension_apply ⟨L y, hL hy⟩]

theorem openDolbeaultD_complexLinearPullback (L : E →L[ℂ] F)
    (hL : MapsTo L (U : Set E) (V : Set F)) (a : Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm V n) :
    DolbeaultOpen.openDolbeaultD n (complexLinearOpenPullback L hL a) =
      complexLinearOpenPullback L hL (DolbeaultOpen.openDolbeaultD n a) := by
  apply Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.ext
  intro x
  rw [DolbeaultOpen.openDolbeaultD_apply, complexLinearOpenPullback_apply, DolbeaultOpen.openDolbeaultD_apply]
  have hd := (complexLinearOpenPullback_extension L hL a x).fderiv_eq (𝕜 := ℝ)
  change alternatizeUncurryFin (Analysis.DifferentialForms.Manifold.ComplexDerivativeParts.complexAntilinearPartCLM E (Analysis.DifferentialForms.Manifold.Basic.FormValue E n)
    (fderiv ℝ (complexLinearOpenPullback L hL a).extension x)) = _
  rw [hd]
  exact LinearDolbeaultPullback.extDerivDoublePrime_complexLinearPullback L
    ((a.smooth.contDiffAt (V.isOpen.mem_nhds (hL x.property))).differentiableAt (by simp))

theorem complexLinearOpenPullback_hasBidegree (L : E →L[ℂ] F)
    (hL : MapsTo L (U : Set E) (V : Set F)) {a : Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm V n}
    (ha : Open.DolbeaultPrime.OpenFormHasBidegree p q a) : Open.DolbeaultPrime.OpenFormHasBidegree p q (complexLinearOpenPullback L hL a) := by
  intro x z v
  rw [complexLinearOpenPullback_apply]
  change a ⟨L x, hL x.property⟩ (fun i => L ((z : ℂ) • v i)) =
    Analysis.DifferentialForms.Manifold.Bidegree.bidegreeCharacter p q z * a ⟨L x, hL x.property⟩ (fun i => L (v i))
  simp_rw [L.map_smul]
  exact ha ⟨L x, hL x.property⟩ z (fun i => L (v i))

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Complex.LinearOpenPullback
