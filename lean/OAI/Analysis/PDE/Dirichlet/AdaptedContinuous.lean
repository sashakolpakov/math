import OAI.Analysis.PDE.Dirichlet.Boundary.Tangential
import OAI.Analysis.PDE.Dirichlet.AdaptedField

open scoped Topology InnerProductSpace Matrix

noncomputable section
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Calculus.Quaternion

def covectorNormal {n : ℕ} (g : CoordinateSpace n 4 →L[ℝ] ℝ) : CoordinateSpace n 4 :=
  ‖g‖⁻¹ • (InnerProductSpace.toDual ℝ (CoordinateSpace n 4)).symm g

theorem covectorNormal_unit {n : ℕ} {g : CoordinateSpace n 4 →L[ℝ] ℝ} (hg : g ≠ 0) :
    ‖covectorNormal g‖ = 1 := by
  simp only [covectorNormal, norm_smul, Real.norm_eq_abs, abs_inv, abs_norm,
    LinearIsometryEquiv.norm_map]
  exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr hg)

theorem covectorNormal_form {n : ℕ} {g : CoordinateSpace n 4 →L[ℝ] ℝ} (hg : g ≠ 0) :
    g = ‖g‖ • innerSL ℝ (covectorNormal g) := by
  ext w
  simp only [covectorNormal, smul_apply, innerSL_apply_apply, real_inner_smul_left, smul_eq_mul]
  rw [← mul_assoc, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hg), one_mul]
  exact InnerProductSpace.toDual_symm_apply.symm

def adaptedTangent {n : ℕ} (g : CoordinateSpace n 4 →L[ℝ] ℝ)
    (H : CoordinateSpace n 4 →L[ℝ] CoordinateSpace n 4 →L[ℝ] ℝ)
    (e : CoordinateSpace n 4) : CoordinateSpace n 4 :=
  ‖g‖⁻¹ • realTangentProjection (covectorNormal g)
    ((InnerProductSpace.toDual ℝ (CoordinateSpace n 4)).symm (H.flip e))

def adaptedRotation {n : ℕ} (g : CoordinateSpace n 4 →L[ℝ] ℝ)
    (H : CoordinateSpace n 4 →L[ℝ] CoordinateSpace n 4 →L[ℝ] ℝ)
    (e : CoordinateSpace n 4) : Matrix (Fin n) (Fin n) Q :=
  rigidMotionMatrix (OAI.Analysis.Calculus.Quaternion.gradientMap OAI.Analysis.Calculus.Quaternion.fourSlots (covectorNormal g))
    (OAI.Analysis.Calculus.Quaternion.gradientMap OAI.Analysis.Calculus.Quaternion.fourSlots (adaptedTangent g H e))

theorem adaptedTangent_tangent {n : ℕ} {g : CoordinateSpace n 4 →L[ℝ] ℝ}
    (hg : g ≠ 0) (H : CoordinateSpace n 4 →L[ℝ] CoordinateSpace n 4 →L[ℝ] ℝ)
    (e : CoordinateSpace n 4) : ⟪covectorNormal g, adaptedTangent g H e⟫_ℝ = 0 := by
  simp only [adaptedTangent, real_inner_smul_right,
    realTangentProjection_tangent (covectorNormal_unit hg), mul_zero]

theorem adaptedRotation_spec {n : ℕ} {g : CoordinateSpace n 4 →L[ℝ] ℝ}
    (hg : g ≠ 0) (H : CoordinateSpace n 4 →L[ℝ] CoordinateSpace n 4 →L[ℝ] ℝ)
    (e : CoordinateSpace n 4) :
    (adaptedRotation g H e)ᴴ = -adaptedRotation g H e ∧
      realMatrixAction (realRepresentation (adaptedRotation g H e)) (covectorNormal g) =
        adaptedTangent g H e := by
  have ht : (quaternionPairing (OAI.Analysis.Calculus.Quaternion.gradientMap OAI.Analysis.Calculus.Quaternion.fourSlots (covectorNormal g))
      (OAI.Analysis.Calculus.Quaternion.gradientMap OAI.Analysis.Calculus.Quaternion.fourSlots (adaptedTangent g H e))).re = 0 := by
    rw [quaternionPairing_gradient_re, adaptedTangent_tangent hg]
  have hu : quaternionPairing (OAI.Analysis.Calculus.Quaternion.gradientMap OAI.Analysis.Calculus.Quaternion.fourSlots (covectorNormal g))
      (OAI.Analysis.Calculus.Quaternion.gradientMap OAI.Analysis.Calculus.Quaternion.fourSlots (covectorNormal g)) = 1 := by
    rw [quaternionPairing_gradient_self, covectorNormal_unit hg]
    simp
  refine ⟨rigidMotionMatrix_skew _ _ ht, ?_⟩
  have hh : OAI.Analysis.Calculus.Quaternion.gradientMap OAI.Analysis.Calculus.Quaternion.fourSlots
      (realMatrixAction (realRepresentation (adaptedRotation g H e)) (covectorNormal g)) =
      OAI.Analysis.Calculus.Quaternion.gradientMap OAI.Analysis.Calculus.Quaternion.fourSlots (adaptedTangent g H e) := by
    rw [gradientMap_realMatrixAction]
    exact rigidMotionMatrix_normal _ _ hu ht
  have heq := OAI.Analysis.Calculus.Quaternion.gradientMap_fourSlots_injective hh
  ext i
  exact congrFun heq i

theorem adaptedRotation_jet {n : ℕ} {g : CoordinateSpace n 4 →L[ℝ] ℝ}
    (hg : g ≠ 0) (H : CoordinateSpace n 4 →L[ℝ] CoordinateSpace n 4 →L[ℝ] ℝ)
    (e : CoordinateSpace n 4) :
    g (realMatrixAction (realRepresentation (adaptedRotation g H e)) (covectorNormal g)) = 0 ∧
    ∀ w, g w = 0 → g (realMatrixAction (realRepresentation (adaptedRotation g H e)) w) + H w e = 0 := by
  obtain ⟨hskew, hact⟩ := adaptedRotation_spec hg H e
  have hgval (w) : g w = ‖g‖ * ⟪covectorNormal g, w⟫_ℝ := by
    conv_lhs => rw [covectorNormal_form hg]
    rfl
  constructor
  · rw [hact, hgval, adaptedTangent_tangent hg, mul_zero]
  intro w hw
  have hwν : ⟪covectorNormal g, w⟫_ℝ = 0 := by
    exact (mul_eq_zero.mp ((hgval w).symm.trans hw)).resolve_left (norm_ne_zero_iff.mpr hg)
  have hvw : ⟪adaptedTangent g H e, w⟫_ℝ = ‖g‖⁻¹ * H w e := by
    simp only [adaptedTangent, realTangentProjection, real_inner_smul_left,
      inner_sub_left, hwν, mul_zero, sub_zero, InnerProductSpace.toDual_symm_apply,
      ContinuousLinearMap.flip_apply]
  rw [hgval, realMatrixAction_skew (realRepresentation_skew hskew), hact, hvw]
  rw [mul_neg, ← mul_assoc, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hg), one_mul]
  ring

section Continuity
variable {X : Type*} [TopologicalSpace X] {x : X} {n : ℕ}

theorem continuousAt_covectorNormal {g : X → CoordinateSpace n 4 →L[ℝ] ℝ}
    (hg : ContinuousAt g x) (hne : g x ≠ 0) :
    ContinuousAt (fun y ↦ covectorNormal (g y)) x := by
  exact (hg.norm.inv₀ (norm_ne_zero_iff.mpr hne)).smul
    ((InnerProductSpace.toDual ℝ (CoordinateSpace n 4)).symm.continuous.continuousAt.comp hg)

theorem continuousAt_adaptedTangent {g : X → CoordinateSpace n 4 →L[ℝ] ℝ}
    {H : X → CoordinateSpace n 4 →L[ℝ] CoordinateSpace n 4 →L[ℝ] ℝ}
    {e : X → CoordinateSpace n 4} (hg : ContinuousAt g x) (hH : ContinuousAt H x)
    (he : ContinuousAt e x) (hne : g x ≠ 0) :
    ContinuousAt (fun y ↦ adaptedTangent (g y) (H y) (e y)) x := by
  have hν := continuousAt_covectorNormal hg hne
  have hf : ContinuousAt (fun y ↦ (H y).flip (e y)) x :=
    ((ContinuousLinearMap.flipₗᵢ ℝ (CoordinateSpace n 4) (CoordinateSpace n 4) ℝ).continuous.continuousAt.comp hH).clm_apply he
  have hz := (InnerProductSpace.toDual ℝ (CoordinateSpace n 4)).symm.continuous.continuousAt.comp hf
  exact (hg.norm.inv₀ (norm_ne_zero_iff.mpr hne)).smul
    (hz.sub ((hν.inner (𝕜 := ℝ) hz).smul hν))

theorem continuousAt_rigidMotionMatrix {ν v : X → Fin n → Q}
    (hν : ContinuousAt ν x) (hv : ContinuousAt v x) :
    ContinuousAt (fun y ↦ rigidMotionMatrix (ν y) (v y)) x := by
  have hp : Continuous (fun p : (Fin n → Q) × (Fin n → Q) ↦ quaternionPairing p.1 p.2) :=
    continuous_quaternionPairing continuous_fst continuous_snd
  have hc : Continuous (fun p : (Fin n → Q) × (Fin n → Q) ↦ rigidMotionMatrix p.1 p.2) := by
    have hνi (i : Fin n) : Continuous (fun p : (Fin n → Q) × (Fin n → Q) ↦ p.1 i) :=
      (continuous_apply i).comp continuous_fst
    have hvi (i : Fin n) : Continuous (fun p : (Fin n → Q) × (Fin n → Q) ↦ p.2 i) :=
      (continuous_apply i).comp continuous_snd
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    exact (((hvi i).mul (hνi j).star).sub ((hνi i).mul (hvi j).star)).sub
      (((hνi i).mul hp).mul (hνi j).star)
  exact hc.continuousAt.comp (f := fun y ↦ (ν y, v y)) (hν.prodMk hv)

theorem continuousAt_adaptedRotation {g : X → CoordinateSpace n 4 →L[ℝ] ℝ}
    {H : X → CoordinateSpace n 4 →L[ℝ] CoordinateSpace n 4 →L[ℝ] ℝ}
    {e : X → CoordinateSpace n 4} (hg : ContinuousAt g x) (hH : ContinuousAt H x)
    (he : ContinuousAt e x) (hne : g x ≠ 0) :
    ContinuousAt (fun y ↦ adaptedRotation (g y) (H y) (e y)) x := by
  apply continuousAt_rigidMotionMatrix
  · exact (gradientCoordinateCLM OAI.Analysis.Calculus.Quaternion.fourSlots).continuous.continuousAt.comp
      (continuousAt_covectorNormal hg hne)
  · exact (gradientCoordinateCLM OAI.Analysis.Calculus.Quaternion.fourSlots).continuous.continuousAt.comp
      (continuousAt_adaptedTangent hg hH he hne)

end Continuity

theorem continuous_boundaryRotation {P : Type*} [TopologicalSpace P] {n : ℕ}
    {r : CoordinateSpace n 4 → ℝ} (hr : ContDiff ℝ 2 r)
    {z e : P → CoordinateSpace n 4} (hz : Continuous z) (he : Continuous e)
    (hreg : ∀ p, fderiv ℝ r (z p) ≠ 0) :
    Continuous (fun p ↦ adaptedRotation (fderiv ℝ r (z p))
      (fderiv ℝ (fderiv ℝ r) (z p)) (e p)) := by
  have hD : ContDiff ℝ 1 (fderiv ℝ r) := hr.fderiv_right (by norm_num)
  have hD2 : Continuous (fderiv ℝ (fderiv ℝ r)) :=
    (hD.fderiv_right (m := 0) (by norm_num)).continuous
  rw [continuous_iff_continuousAt]
  intro p
  exact continuousAt_adaptedRotation (hD.continuous.comp hz).continuousAt
    (hD2.comp hz).continuousAt he.continuousAt (hreg p)

end OAI.Analysis.PDE.Dirichlet
