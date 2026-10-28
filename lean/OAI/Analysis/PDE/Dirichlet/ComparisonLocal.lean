import OAI.Analysis.PDE.Dirichlet.Periodic.Comparison
import OAI.Analysis.PDE.Elliptic.Boundary.LocalExtension

open Set Filter Module
open scoped Topology Matrix ComplexOrder
noncomputable section
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Calculus.Quaternion OAI.LinearAlgebra.Moore

theorem quaternionHessian_congr_germ {m s : ℕ} (e : Fin s → Quaternion ℝ)
    {f g : CoordinateSpace m s → ℝ} {x : CoordinateSpace m s}
    (hfg : f =ᶠ[𝓝 x] g) : quaternionHessian e f x = quaternionHessian e g x := by
  have hD := (hfg.fderiv (𝕜 := ℝ)).fderiv_eq (𝕜 := ℝ)
  change OAI.Analysis.Calculus.Quaternion.hessianMap e
      (fun i j ↦ fderiv ℝ (fderiv ℝ f) x (coordinateVector i) (coordinateVector j)) =
    OAI.Analysis.Calculus.Quaternion.hessianMap e
      (fun i j ↦ fderiv ℝ (fderiv ℝ g) x (coordinateVector i) (coordinateVector j))
  rw [hD]

theorem exists_contDiff_extension_near_point {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {f : E → ℝ} {k : ℕ} {x : E} (hf : ContDiffAt ℝ k f x) :
    ∃ g : E → ℝ, ContDiff ℝ k g ∧ g =ᶠ[𝓝 x] f := by
  obtain ⟨g, hg, heq⟩ := OAI.Analysis.PDE.Elliptic.exists_contDiff_extension_near_compact
    (K := {x}) isCompact_singleton (fun y hy ↦ by
      have hyx : y = x := mem_singleton_iff.mp hy
      simpa only [hyx] using hf)
  exact ⟨g, hg, heq x (mem_singleton x)⟩

/-- The nonlinear maximum argument needs C² regularity only near the
interior maximizing point, not an extension through the physical boundary. -/
theorem quaternionHessian_gap_posDef_of_barrier_at {n : ℕ}
    {f g r : CoordinateSpace n 4 → ℝ} {x : CoordinateSpace n 4}
    (hf : ContDiffAt ℝ 2 f x) (hg : ContDiffAt ℝ 2 g x) (hr : ContDiffAt ℝ 2 r x)
    {ε : ℝ} (hε : 0 < ε)
    (hrpos : (OAI.LinearAlgebra.Moore.complexify (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots r x)).PosDef)
    (hmax : IsLocalMax (fun y ↦ (f y + (-1 : ℝ) • g y) + ε • r y) x) :
    (OAI.LinearAlgebra.Moore.complexify (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots g x - quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots f x)).PosDef := by
  obtain ⟨f', hf', hfeq⟩ := exists_contDiff_extension_near_point hf
  obtain ⟨g', hg', hgeq⟩ := exists_contDiff_extension_near_point hg
  obtain ⟨r', hr', hreq⟩ := exists_contDiff_extension_near_point hr
  have heq : (fun y ↦ (f' y + (-1 : ℝ) • g' y) + ε • r' y) =ᶠ[𝓝 x]
      (fun y ↦ (f y + (-1 : ℝ) • g y) + ε • r y) := by
    filter_upwards [hfeq, hgeq, hreq] with y hfy hgy hry
    rw [hfy, hgy, hry]
  have hm : IsLocalMax (fun y ↦ (f' y + (-1 : ℝ) • g' y) + ε • r' y) x := by
    have heqx : (f' x + (-1 : ℝ) • g' x) + ε • r' x =
        (f x + (-1 : ℝ) • g x) + ε • r x := heq.self_of_nhds
    filter_upwards [hmax, heq] with y hy heqy
    rw [heqy, heqx]
    exact hy
  have hR : (OAI.LinearAlgebra.Moore.complexify (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots r' x)).PosDef := by
    rwa [quaternionHessian_congr_germ OAI.Analysis.Calculus.Quaternion.fourSlots hreq]
  have hh := quaternionHessian_gap_posDef_of_barrier hf' hg' hr' hε hR hm
  simpa only [quaternionHessian_congr_germ OAI.Analysis.Calculus.Quaternion.fourSlots hgeq,
    quaternionHessian_congr_germ OAI.Analysis.Calculus.Quaternion.fourSlots hfeq] using hh

end OAI.Analysis.PDE.Dirichlet
