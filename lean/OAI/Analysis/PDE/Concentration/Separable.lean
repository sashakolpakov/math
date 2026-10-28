import OAI.Analysis.PDE.Concentration.Cylinder.LocalCalculus
import OAI.Analysis.PDE.Concentration.Cylinder.Coordinates

namespace OAI.Analysis.PDE.Concentration

open Set Filter Laplacian InnerProductSpace
open scoped ContDiff Topology

noncomputable def cylinderAxisComplement : Set CylinderSpace :=
  {x | (cylinderComplexEquiv x).2 ≠ 0}

theorem contDiff_cylinderComplexCoordinate : ContDiff ℝ ∞ (fun x => (cylinderComplexEquiv x).2) := by
  simp only [cylinderComplexEquiv_apply]
  have h₁ : ContDiff ℝ ∞ (fun x : CylinderSpace => x 1) := by fun_prop
  have h₂ : ContDiff ℝ ∞ (fun x : CylinderSpace => x 2) := by fun_prop
  exact (Complex.ofRealCLM.contDiff.comp h₁).add
    ((Complex.ofRealCLM.contDiff.comp h₂).mul contDiff_const)

theorem isOpen_cylinderAxisComplement : IsOpen cylinderAxisComplement :=
  isOpen_ne_fun contDiff_cylinderComplexCoordinate.continuous continuous_const

noncomputable def cylinderSeparable (w S : ℝ → ℝ) (x : CylinderSpace) : ℝ :=
  w (x 0) * S ‖(cylinderComplexEquiv x).2‖

theorem contDiffOn_cylinderSeparable {w S : ℝ → ℝ} (hw : ContDiff ℝ ∞ w)
    (hS : ContDiffOn ℝ ∞ S (Ioi 0)) :
    ContDiffOn ℝ ∞ (cylinderSeparable w S) cylinderAxisComplement := by
  intro x hx
  have hz : (cylinderComplexEquiv x).2 ≠ 0 := hx
  have hn : ContDiffAt ℝ ∞ (fun y => ‖(cylinderComplexEquiv y).2‖) x :=
    ContDiffAt.norm (𝕜 := ℝ) contDiff_cylinderComplexCoordinate.contDiffAt hz
  have hSc : ContDiffAt ℝ ∞ S ‖(cylinderComplexEquiv x).2‖ :=
    (hS _ (norm_pos_iff.mpr hz)).contDiffAt (isOpen_Ioi.mem_nhds (norm_pos_iff.mpr hz))
  have ht : ContDiff ℝ ∞ (fun y : CylinderSpace => y 0) := by fun_prop
  exact ((hw.contDiffAt.comp x ht.contDiffAt).mul (hSc.comp x hn)).contDiffWithinAt

theorem cylinderSeparable_apply (w S : ℝ → ℝ) (t r θ : ℝ) (hr : 0 ≤ r) :
    cylinderSeparable w S (cylinderPoint t r θ) = w t * S r := by
  have ht : (cylinderPoint t r θ) 0 = t := by
    simp [cylinderPoint, cylinderRadial, cylinderAxis, EuclideanSpace.basisFun_apply]
  simp only [cylinderSeparable, ht, cylinderComplexEquiv_point, Complex.norm_polarCoord_symm,
    abs_of_nonneg hr]

theorem laplacian_cylinderSeparable {w S : ℝ → ℝ} (hw : ContDiff ℝ ∞ w)
    (hS : ContDiffOn ℝ ∞ S (Ioi 0)) (t r θ : ℝ) (hr : 0 < r) :
    Δ (cylinderSeparable w S) (cylinderPoint t r θ) =
      w t * (deriv (deriv S) r + deriv S r / r) + deriv (deriv w) t * S r := by
  have hp : cylinderPoint t r θ ∈ cylinderAxisComplement := by
    change (cylinderComplexEquiv (cylinderPoint t r θ)).2 ≠ 0
    apply norm_pos_iff.mp
    simpa only [cylinderComplexEquiv_point, Complex.norm_polarCoord_symm, abs_of_pos hr] using hr
  have h := cylinder_laplacian_identity_on isOpen_cylinderAxisComplement
    ((contDiffOn_cylinderSeparable hw hS).of_le (by simp)) t r θ hr.ne' hp
  have her : (fun s => cylinderSeparable w S (cylinderPoint t s θ)) =ᶠ[nhds r]
      (fun s => w t * S s) := by
    filter_upwards [isOpen_Ioi.mem_nhds hr] with s hs
    exact cylinderSeparable_apply w S t s θ hs.le
  have hea : (fun s => cylinderSeparable w S (cylinderPoint t r s)) = (fun _ => w t * S r) :=
    funext (fun s => cylinderSeparable_apply w S t r s hr.le)
  have het : (fun s => cylinderSeparable w S (cylinderPoint s r θ)) = (fun s => w s * S r) :=
    funext (fun s => cylinderSeparable_apply w S s r θ hr.le)
  rw [her.deriv.deriv_eq, her.deriv_eq, hea, het] at h
  simp only [deriv_const_mul_field', deriv_const_mul_field, deriv_mul_const_field',
    deriv_mul_const_field, deriv_const] at h
  rw [← h]
  ring

end OAI.Analysis.PDE.Concentration
