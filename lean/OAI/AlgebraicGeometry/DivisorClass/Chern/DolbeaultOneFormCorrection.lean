import OAI.AlgebraicGeometry.DivisorClass.Chern.ScalarDolbeaultCommutation

/-! # Dolbeault One Form Correction -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.DolbeaultOneFormCorrection

noncomputable section

/-! Subtracting an actual scalar Dolbeault derivative removes a coefficient and preserves closedness. -/

open _root_.TopologicalSpace Filter _root_.ContinuousAlternatingMap
open scoped ContDiff _root_.Topology

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] {U : Opens E}

def correctDolbeaultOneForm (a : Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm U 1) (g : E → ℂ)
    (hg : ContDiffOn ℝ ∞ g (U : Set E)) : Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm U 1 :=
  a - DolbeaultOpen.openDolbeaultD 0 (ScalarDolbeaultCommutation.scalarOpenZeroForm U g hg)

theorem correctDolbeaultOneForm_coefficient (a : Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm U 1) {g : E → ℂ}
    (hg : ContDiffOn ℝ ∞ g (U : Set E)) (x : U) (v : E) :
    AntiOneFormCoordinates.oneFormLinear (correctDolbeaultOneForm a g hg x) v =
      AntiOneFormCoordinates.oneFormLinear (a x) v - AntiOneFormCoordinates.antilinearScalarDerivative g x v := by
  change AntiOneFormCoordinates.oneFormLinear (a x - DolbeaultOpen.openDolbeaultD 0 (ScalarDolbeaultCommutation.scalarOpenZeroForm U g hg) x) v = _
  change AntiOneFormCoordinates.oneFormLinearEquiv.symm (a x - DolbeaultOpen.openDolbeaultD 0 (ScalarDolbeaultCommutation.scalarOpenZeroForm U g hg) x) v = _
  rw [map_sub]
  change AntiOneFormCoordinates.oneFormLinear (a x) v - AntiOneFormCoordinates.oneFormLinear (DolbeaultOpen.openDolbeaultD 0 (ScalarDolbeaultCommutation.scalarOpenZeroForm U g hg) x) v = _
  rw [ScalarDolbeaultCommutation.scalarOpenZeroForm_dbar_coefficient hg]

theorem correctDolbeaultOneForm_closed (a : Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm U 1)
    (ha : DolbeaultOpen.openDolbeaultD 1 a = 0) {g : E → ℂ} (hg : ContDiffOn ℝ ∞ g (U : Set E)) :
    DolbeaultOpen.openDolbeaultD 1 (correctDolbeaultOneForm a g hg) = 0 := by
  change DolbeaultOpen.openDolbeaultD 1 (a - DolbeaultOpen.openDolbeaultD 0 (ScalarDolbeaultCommutation.scalarOpenZeroForm U g hg)) = 0
  have hsub : a - DolbeaultOpen.openDolbeaultD 0 (ScalarDolbeaultCommutation.scalarOpenZeroForm U g hg) =
      a + (-1 : ℂ) • DolbeaultOpen.openDolbeaultD 0 (ScalarDolbeaultCommutation.scalarOpenZeroForm U g hg) := by
    apply Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.ext
    intro x
    apply ContinuousAlternatingMap.ext
    intro v
    change a x v - DolbeaultOpen.openDolbeaultD 0 (ScalarDolbeaultCommutation.scalarOpenZeroForm U g hg) x v =
      a x v + (-1 : ℂ) * DolbeaultOpen.openDolbeaultD 0 (ScalarDolbeaultCommutation.scalarOpenZeroForm U g hg) x v
    ring
  rw [hsub, map_add, map_smul, ha, ScalarDolbeaultCommutation.scalarOpenZeroForm_dbar_closed hg, smul_zero, add_zero]

theorem correctDolbeaultOneForm_pure (a : Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm U 1)
    (ha : Open.DolbeaultPrime.OpenFormHasBidegree 0 1 a) {g : E → ℂ} (hg : ContDiffOn ℝ ∞ g (U : Set E)) :
    Open.DolbeaultPrime.OpenFormHasBidegree 0 1 (correctDolbeaultOneForm a g hg) := by
  have hd := Open.DolbeaultPrime.openDolbeaultD_hasBidegree (p := 0) (q := 0) rfl
    (fun x => Analysis.DifferentialForms.Manifold.Bidegree.hasBidegree_zero E (ScalarDolbeaultCommutation.scalarOpenZeroForm U g hg x))
  intro x z v
  change a x (fun i => (z : ℂ) • v i) -
    DolbeaultOpen.openDolbeaultD 0 (ScalarDolbeaultCommutation.scalarOpenZeroForm U g hg) x (fun i => (z : ℂ) • v i) =
    Analysis.DifferentialForms.Manifold.Bidegree.bidegreeCharacter 0 1 z *
      (a x v - DolbeaultOpen.openDolbeaultD 0 (ScalarDolbeaultCommutation.scalarOpenZeroForm U g hg) x v)
  rw [ha x z v, hd x z v, mul_sub]

theorem correctDolbeaultOneForm_coefficient_zero (a : Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm U 1) {g : E → ℂ}
    (hg : ContDiffOn ℝ ∞ g (U : Set E)) (e : E)
    (he : ∀ x : U, AntiOneFormCoordinates.antilinearScalarDerivative g x e = AntiOneFormCoordinates.oneFormLinear (a x) e) :
    ∀ x : U, AntiOneFormCoordinates.oneFormLinear (correctDolbeaultOneForm a g hg x) e = 0 := by
  intro x
  rw [correctDolbeaultOneForm_coefficient, he x, sub_self]

theorem closed_oneForm_zero_coefficient_derivative (a : Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm U 1)
    (ha : DolbeaultOpen.openDolbeaultD 1 a = 0) (e : E) (he : ∀ x : U, AntiOneFormCoordinates.oneFormLinear (a x) e = 0)
    (x : U) (v : E) :
    AntiOneFormCoordinates.antilinearScalarDerivative (fun y => AntiOneFormCoordinates.oneFormLinear (a.extension y) v) x e = 0 := by
  have hs := AntiOneFormCoordinates.closed_oneForm_scalar_symmetry
    ((a.smooth.contDiffAt (U.isOpen.mem_nhds x.property)).differentiableAt (by simp))
    ((DolbeaultOpen.openDolbeaultD_zero_iff a).mp ha x) e v
  have heq : (fun y => AntiOneFormCoordinates.oneFormLinear (a.extension y) e) =ᶠ[𝓝 (x : E)] 0 := by
    filter_upwards [U.isOpen.mem_nhds x.property] with y hy
    rw [show a.extension y = a ⟨y, hy⟩ from a.extension_apply ⟨y, hy⟩]
    exact he ⟨y, hy⟩
  rw [hs, ScalarDolbeaultCommutation.antilinearScalarDerivative_congr heq]
  unfold AntiOneFormCoordinates.antilinearScalarDerivative
  have hzero : fderiv ℝ (0 : E → ℂ) (x : E) = 0 := (hasFDerivAt_const (0 : ℂ) (x : E)).fderiv
  rw [hzero, (Analysis.DifferentialForms.Manifold.ComplexDerivativeParts.complexAntilinearPartCLM E ℂ).map_zero]
  rfl

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.DolbeaultOneFormCorrection
