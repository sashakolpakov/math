import OAI.AlgebraicGeometry.DivisorClass.Chern.AntiOneFormCoordinates
import OAI.AlgebraicGeometry.DivisorClass.Chern.Open.DolbeaultSquared

/-! # Scalar Dolbeault Commutation -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.ScalarDolbeaultCommutation

noncomputable section

section

/-! Actual smooth scalar zero-forms and their antiholomorphic one-form coefficients. -/

open _root_.ContinuousAlternatingMap _root_.TopologicalSpace Filter
open scoped ContDiff _root_.Topology

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

def scalarOpenZeroForm (U : Opens E) (f : E → ℂ) (hf : ContDiffOn ℝ ∞ f (U : Set E)) :
    Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm U 0 :=
  Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.ofRaw U (fun x => constOfIsEmpty ℝ E (Fin 0) (f x))
    ((constOfIsEmptyLIE ℝ E ℂ (Fin 0)).contDiff.comp_contDiffOn hf)

variable [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]

theorem scalarOpenZeroForm_dbar {U : Opens E} {f : E → ℂ}
    (hf : ContDiffOn ℝ ∞ f (U : Set E)) (x : U) :
    DolbeaultOpen.openDolbeaultD 0 (scalarOpenZeroForm U f hf) x =
      ofSubsingleton ℝ E ℂ (0 : Fin 1) (Analysis.DifferentialForms.Manifold.ComplexDerivativeParts.complexAntilinearPartCLM E ℂ (fderiv ℝ f x)) := by
  have he := Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.extension_ofRaw_eventuallyEq
    (fun y => constOfIsEmpty ℝ E (Fin 0) (f y))
    ((constOfIsEmptyLIE ℝ E ℂ (Fin 0)).contDiff.comp_contDiffOn hf) x
  have hd : fderiv ℝ (scalarOpenZeroForm U f hf).extension (x : E) =
      fderiv ℝ (fun y => constOfIsEmpty ℝ E (Fin 0) (f y)) (x : E) := he.fderiv_eq
  change alternatizeUncurryFin (Analysis.DifferentialForms.Manifold.ComplexDerivativeParts.complexAntilinearPartCLM E (Analysis.DifferentialForms.Manifold.Basic.FormValue E 0)
    (fderiv ℝ (scalarOpenZeroForm U f hf).extension x)) = _
  rw [hd]
  exact DolbeaultZeroForms.extDerivDoublePrime_constOfIsEmpty f x

theorem scalarOpenZeroForm_dbar_coefficient {U : Opens E} {f : E → ℂ}
    (hf : ContDiffOn ℝ ∞ f (U : Set E)) (x : U) (v : E) :
    AntiOneFormCoordinates.oneFormLinear (DolbeaultOpen.openDolbeaultD 0 (scalarOpenZeroForm U f hf) x) v =
      AntiOneFormCoordinates.antilinearScalarDerivative f x v := by
  rw [scalarOpenZeroForm_dbar hf]
  rfl

theorem scalarOpenZeroForm_dbar_closed {U : Opens E} {f : E → ℂ}
    (hf : ContDiffOn ℝ ∞ f (U : Set E)) :
    DolbeaultOpen.openDolbeaultD 1 (DolbeaultOpen.openDolbeaultD 0 (scalarOpenZeroForm U f hf)) = 0 :=
  Open.DolbeaultSquared.openDolbeaultD_squared_of_bidegree (scalarOpenZeroForm U f hf) (p := 0) (q := 0) rfl
    (fun x => Analysis.DifferentialForms.Manifold.Bidegree.hasBidegree_zero E (scalarOpenZeroForm U f hf x))

theorem antilinearScalarDerivative_congr {f g : E → ℂ} {x : E}
    (h : f =ᶠ[𝓝 x] g) (v : E) :
    AntiOneFormCoordinates.antilinearScalarDerivative f x v = AntiOneFormCoordinates.antilinearScalarDerivative g x v := by
  unfold AntiOneFormCoordinates.antilinearScalarDerivative
  rw [h.fderiv_eq]

theorem scalarOpenZeroForm_dbar_extension_coefficient {U : Opens E} {f : E → ℂ}
    (hf : ContDiffOn ℝ ∞ f (U : Set E)) (x : U) (v : E) :
    (fun y => AntiOneFormCoordinates.oneFormLinear ((DolbeaultOpen.openDolbeaultD 0 (scalarOpenZeroForm U f hf)).extension y) v) =ᶠ[𝓝 (x : E)]
      (fun y => AntiOneFormCoordinates.antilinearScalarDerivative f y v) := by
  filter_upwards [U.isOpen.mem_nhds x.property] with y hy
  rw [show (DolbeaultOpen.openDolbeaultD 0 (scalarOpenZeroForm U f hf)).extension y =
    DolbeaultOpen.openDolbeaultD 0 (scalarOpenZeroForm U f hf) ⟨y, hy⟩ from Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.extension_apply _ ⟨y, hy⟩]
  exact scalarOpenZeroForm_dbar_coefficient hf ⟨y, hy⟩ v

end

/-! Mixed scalar antiholomorphic derivatives commute by the original square-zero form identity. -/

open _root_.TopologicalSpace
open scoped ContDiff _root_.Topology

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]

theorem antilinearScalarDerivative_commute {U : Opens E} {f : E → ℂ}
    (hf : ContDiffOn ℝ ∞ f (U : Set E)) (x : U) (v w : E) :
    AntiOneFormCoordinates.antilinearScalarDerivative (fun y => AntiOneFormCoordinates.antilinearScalarDerivative f y w) x v =
      AntiOneFormCoordinates.antilinearScalarDerivative (fun y => AntiOneFormCoordinates.antilinearScalarDerivative f y v) x w := by
  let a : Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm U 1 := DolbeaultOpen.openDolbeaultD 0 (scalarOpenZeroForm U f hf)
  have ha : DifferentiableAt ℝ a.extension (x : E) :=
    (a.smooth.contDiffAt (U.isOpen.mem_nhds x.property)).differentiableAt (by simp)
  have hclosed : Analysis.DifferentialForms.Manifold.DolbeaultLocal.extDerivDoublePrime a.extension (x : E) = 0 :=
    (DolbeaultOpen.openDolbeaultD_zero_iff a).mp (scalarOpenZeroForm_dbar_closed hf) x
  have h := AntiOneFormCoordinates.closed_oneForm_scalar_symmetry ha hclosed v w
  have hleft := antilinearScalarDerivative_congr
    (scalarOpenZeroForm_dbar_extension_coefficient hf x w) v
  have hright := antilinearScalarDerivative_congr
    (scalarOpenZeroForm_dbar_extension_coefficient hf x v) w
  exact hleft.symm.trans (h.trans hright)

theorem antilinearScalarDerivative_smooth {U : Opens E} {f : E → ℂ}
    (hf : ContDiffOn ℝ ∞ f (U : Set E)) (v : E) :
    ContDiffOn ℝ ∞ (fun x => AntiOneFormCoordinates.antilinearScalarDerivative f x v) (U : Set E) := by
  let a : Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm U 1 := DolbeaultOpen.openDolbeaultD 0 (scalarOpenZeroForm U f hf)
  apply (AntiOneFormCoordinates.openOneForm_coefficient_smooth a v).congr
  intro x hx
  rw [show a.extension x = a ⟨x, hx⟩ from a.extension_apply ⟨x, hx⟩]
  exact (scalarOpenZeroForm_dbar_coefficient hf ⟨x, hx⟩ v).symm

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.ScalarDolbeaultCommutation
