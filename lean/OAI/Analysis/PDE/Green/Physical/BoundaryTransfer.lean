import OAI.Analysis.PDE.Green.Physical.FullProjection
import OAI.Analysis.PDE.Green.BoundedGreen

/-! Exact boundary jets under extension of the rational physical defining function. -/

noncomputable section
namespace OAI.Analysis.PDE.Green

open Set Filter Matrix OAI.Analysis.Calculus.Current OAI.Analysis.Calculus.Quaternion OAI.Analysis.PDE.Dirichlet
open scoped Topology Matrix.Norms.Elementwise

def physicalFullDefining (d : ℕ) (a : ℝ) (x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 2) 3) : ℝ :=
  OAI.Analysis.Calculus.Current.physicalFiberDefining (1 / 10) a (fullPhysicalProjection d x).1 (fullPhysicalProjection d x).2

theorem quaternionGradient_congr_nhds {n s : ℕ} (e : Fin s → Quaternion ℝ)
    {f g : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s → ℝ} {x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s} (h : f =ᶠ[𝓝 x] g) :
    OAI.Analysis.PDE.Dirichlet.quaternionGradient e f x = OAI.Analysis.PDE.Dirichlet.quaternionGradient e g x := by
  unfold OAI.Analysis.PDE.Dirichlet.quaternionGradient
  rw [realGradient_congr_nhds h]

theorem physical_extension_boundary_germ {d : ℕ} (a : ℝ)
    (R : (ℂ × (Option (Fin d) → ℂ)) → ℝ) {T : Set ℂ}
    (heq : ∀ τ ∈ T, ∀ q, OAI.Analysis.Calculus.Current.physicalFiberDefining (1 / 10) a τ q ≤ 0 →
      R =ᶠ[𝓝 (τ, q)] (fun p => OAI.Analysis.Calculus.Current.physicalFiberDefining (1 / 10) a p.1 p.2))
    (hnonpos : ∀ τ ∈ T, ∀ q, R (τ, q) ≤ 0 ↔ OAI.Analysis.Calculus.Current.physicalFiberDefining (1 / 10) a τ q ≤ 0)
    {x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 2) 3} (hxT : (fullPhysicalProjection d x).1 ∈ T)
    (hx : R (fullPhysicalProjection d x) = 0) :
    (fun y => R (fullPhysicalProjection d y)) =ᶠ[𝓝 x] physicalFullDefining d a := by
  have hraw := (hnonpos _ hxT _).mp hx.le
  exact (heq _ hxT _ hraw).comp_tendsto ((fullPhysicalProjection d).continuous.tendsto x)

theorem physical_extension_local_boundary_data {d : ℕ} (a : ℝ)
    (R : (ℂ × (Option (Fin d) → ℂ)) → ℝ) {T : Set ℂ}
    (heq : ∀ τ ∈ T, ∀ q, OAI.Analysis.Calculus.Current.physicalFiberDefining (1 / 10) a τ q ≤ 0 →
      R =ᶠ[𝓝 (τ, q)] (fun p => OAI.Analysis.Calculus.Current.physicalFiberDefining (1 / 10) a p.1 p.2))
    (hnonpos : ∀ τ ∈ T, ∀ q, R (τ, q) ≤ 0 ↔ OAI.Analysis.Calculus.Current.physicalFiberDefining (1 / 10) a τ q ≤ 0)
    (hT : ∀ τ ∈ T, a < ‖τ‖ ∧ ‖τ‖ < 4)
    (e : Fin 3 → Quaternion ℝ)
    (A : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 2) 3 → Matrix (Fin (d + 2)) (Fin (d + 2)) (Quaternion ℝ))
    (u : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 2) 3 → ℝ) (ε G : ℝ)
    (hdata : ∀ x, (a < ‖(fullPhysicalProjection d x).1‖ ∧ ‖(fullPhysicalProjection d x).1‖ < 4) →
      physicalFullDefining d a x = 0 → u x = 0 ∧
        ‖star (OAI.Analysis.PDE.Dirichlet.quaternionGradient e (physicalFullDefining d a) x) ᵥ* A x‖ ≤ ε ∧
        ‖OAI.Analysis.PDE.Dirichlet.quaternionGradient e u x‖ ≤ G)
    {x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 2) 3} (hxT : (fullPhysicalProjection d x).1 ∈ T)
    (hx : R (fullPhysicalProjection d x) = 0) :
    ∀ᶠ y in 𝓝 x, R (fullPhysicalProjection d y) = 0 → u y = 0 ∧
      ‖star (OAI.Analysis.PDE.Dirichlet.quaternionGradient e (fun z => R (fullPhysicalProjection d z)) y) ᵥ* A y‖ ≤ ε ∧
      ‖OAI.Analysis.PDE.Dirichlet.quaternionGradient e u y‖ ≤ G := by
  have hg := physical_extension_boundary_germ a R heq hnonpos hxT hx
  have hg' := eventually_eventually_nhds.mpr hg
  have hc : Continuous (fun y : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 2) 3 => ‖(fullPhysicalProjection d y).1‖) :=
    (continuous_fst.comp (fullPhysicalProjection d).continuous).norm
  have hann : ∀ᶠ y in 𝓝 x,
      a < ‖(fullPhysicalProjection d y).1‖ ∧ ‖(fullPhysicalProjection d y).1‖ < 4 :=
    ((isOpen_lt continuous_const hc).inter (isOpen_lt hc continuous_const)).mem_nhds (hT _ hxT)
  filter_upwards [hg', hann] with y hy hya hyr
  change (fun z => R (fullPhysicalProjection d z)) =ᶠ[𝓝 y] physicalFullDefining d a at hy
  have hd := hdata y hya (hy.eq_of_nhds.symm.trans hyr)
  rw [quaternionGradient_congr_nhds e hy]
  exact hd

theorem physical_extension_common_kernel {d : ℕ} (a : ℝ)
    (R : (ℂ × (Option (Fin d) → ℂ)) → ℝ) {T : Set ℂ}
    (heq : ∀ τ ∈ T, ∀ q, OAI.Analysis.Calculus.Current.physicalFiberDefining (1 / 10) a τ q ≤ 0 →
      R =ᶠ[𝓝 (τ, q)] (fun p => OAI.Analysis.Calculus.Current.physicalFiberDefining (1 / 10) a p.1 p.2))
    (hnonpos : ∀ τ ∈ T, ∀ q, R (τ, q) ≤ 0 ↔ OAI.Analysis.Calculus.Current.physicalFiberDefining (1 / 10) a τ q ≤ 0)
    (e : Fin 3 → Quaternion ℝ) (B : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 2) 3 → ℝ)
    {x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 2) 3} (hxT : (fullPhysicalProjection d x).1 ∈ T)
    (hx : R (fullPhysicalProjection d x) = 0)
    (hker : ∃ w : Fin (d + 2) → Quaternion ℝ, w ≠ 0 ∧
      OAI.Analysis.PDE.Dirichlet.quaternionHessian e (physicalFullDefining d a) x *ᵥ w = 0 ∧ OAI.Analysis.PDE.Dirichlet.quaternionHessian e B x *ᵥ w = 0 ∧
      star (OAI.Analysis.PDE.Dirichlet.quaternionGradient e (physicalFullDefining d a) x) ⬝ᵥ w = 0) :
    ∃ w : Fin (d + 2) → Quaternion ℝ, w ≠ 0 ∧
      OAI.Analysis.PDE.Dirichlet.quaternionHessian e (fun y => R (fullPhysicalProjection d y)) x *ᵥ w = 0 ∧
      OAI.Analysis.PDE.Dirichlet.quaternionHessian e B x *ᵥ w = 0 ∧
      star (OAI.Analysis.PDE.Dirichlet.quaternionGradient e (fun y => R (fullPhysicalProjection d y)) x) ⬝ᵥ w = 0 := by
  have hg := physical_extension_boundary_germ a R heq hnonpos hxT hx
  rw [quaternionHessian_congr_nhds e hg, quaternionGradient_congr_nhds e hg]
  exact hker

end OAI.Analysis.PDE.Green
