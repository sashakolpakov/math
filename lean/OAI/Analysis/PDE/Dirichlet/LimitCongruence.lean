import OAI.Analysis.PDE.Dirichlet.LocalSolutionLimit

open Set Filter
open scoped Topology
noncomputable section
namespace OAI.Analysis.PDE.Dirichlet

theorem locally_uniform_limit_congr_on {E Y : Type*} [TopologicalSpace E] [UniformSpace Y]
    {u : ℕ → E → Y} {f g : E → Y} {Ω : Set E}
    (h : TendstoLocallyUniformlyOn u f atTop Ω) (hfg : EqOn g f Ω) :
    TendstoLocallyUniformlyOn u g atTop Ω := by
  rw [tendstoLocallyUniformlyOn_iff_tendstoLocallyUniformly_comp_coe] at h ⊢
  have heq : g ∘ ((↑) : Ω → E) = f ∘ (↑) := funext (fun x ↦ hfg x.property)
  rwa [heq]

theorem fderiv_eqOn_of_open {E Y : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {f g : E → Y} {Ω : Set E} (hΩ : IsOpen Ω) (hfg : EqOn f g Ω) :
    EqOn (fderiv ℝ f) (fderiv ℝ g) Ω := by
  intro x hx
  have heq : f =ᶠ[𝓝 x] g := by
    filter_upwards [hΩ.mem_nhds hx] with y hy
    exact hfg hy
  exact heq.fderiv_eq

theorem quaternionHessian_eqOn_of_open {m s : ℕ} (e : Fin s → Quaternion ℝ)
    {f g : CoordinateSpace m s → ℝ} {Ω : Set (CoordinateSpace m s)}
    (hΩ : IsOpen Ω) (hfg : EqOn f g Ω) :
    EqOn (quaternionHessian e f) (quaternionHessian e g) Ω := by
  intro x hx
  have hD := fderiv_eqOn_of_open hΩ (fderiv_eqOn_of_open hΩ hfg) hx
  change OAI.Analysis.Calculus.Quaternion.hessianMap e
      (fun i j ↦ fderiv ℝ (fderiv ℝ f) x (coordinateVector i) (coordinateVector j)) =
    OAI.Analysis.Calculus.Quaternion.hessianMap e
      (fun i j ↦ fderiv ℝ (fderiv ℝ g) x (coordinateVector i) (coordinateVector j))
  rw [hD]

end OAI.Analysis.PDE.Dirichlet
