import OAI.Analysis.PDE.Elliptic.Boundary.PhysicalHolder
import OAI.Analysis.PDE.Elliptic.Boundary.CompactHolder

/-! A uniform Hölder modulus for the actual Hessian trace on any compact
regular part of the boundary, for a family of nonlinear Dirichlet solutions. -/

noncomputable section
namespace OAI.Analysis.PDE.Elliptic

open Set InnerProductSpace OAI.Analysis.PDE.Dirichlet OAI.Analysis.Calculus.Quaternion OAI.LinearAlgebra.Moore
open scoped Topology Matrix ComplexOrder

theorem boundary_hessian_holder_on_compact {n : ℕ} [Nonempty (Fin n)]
    {P : Type*} {r B : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4 → ℝ}
    (hr : ContDiff ℝ 3 r) (hB : ContDiff ℝ 3 B)
    {U K : Set (OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4)} (hU : IsOpen U) (hK : IsCompact K)
    (hKU : K ⊆ U) (hKr : ∀ x ∈ K, r x = 0)
    (hreg : ∀ x ∈ K, fderiv ℝ r x ≠ 0)
    {lam V : ℝ} (hlam : 0 < lam) (hV : 0 < V)
    (u f : P → OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4 → ℝ)
    (hu : ∀ p, ContDiff ℝ 3 (u p)) (hf : ∀ p, Continuous (f p))
    (hDu : ∀ p y, y ∈ U → r y ≤ 0 → ‖fderiv ℝ (u p) y‖ ≤ V)
    (hD2u : ∀ p y, y ∈ U → r y ≤ 0 → ‖fderiv ℝ (gradient (u p)) y‖ ≤ V)
    (hpos : ∀ p y, y ∈ U → r y ≤ 0 →
      (OAI.LinearAlgebra.Moore.complexify (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (u p) y)).PosDef)
    (hA : ∀ p y, y ∈ U → r y ≤ 0 →
      ‖OAI.Analysis.PDE.Dirichlet.logRealOperator (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (u p) y)‖ ≤ V)
    (hlo : ∀ p y, y ∈ U → r y ≤ 0 → ∀ w,
      lam * ‖w‖ ^ 2 ≤ inner ℝ w (OAI.Analysis.PDE.Dirichlet.logRealOperator (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (u p) y) w))
    (hdf : ∀ p y, y ∈ U → r y ≤ 0 → DifferentiableAt ℝ (f p) y)
    (hfne : ∀ p y, y ∈ U → r y ≤ 0 → f p y ≠ 0)
    (hf1 : ∀ p y, y ∈ U → r y ≤ 0 → ‖fderiv ℝ (f p) y‖ / |f p y| ≤ V)
    (heq : ∀ p y, y ∈ U → r y < 0 →
      OAI.LinearAlgebra.Moore.mooreDet n (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (u p) y) = f p y)
    (hzero : ∀ p y, y ∈ U → r y = 0 → u p y = B y) :
    ∃ α C : ℝ, 0 < α ∧ α < 1 ∧ 0 < C ∧
      ∀ p y, y ∈ K → ∀ z, z ∈ K →
        ‖fderiv ℝ (gradient (u p)) y - fderiv ℝ (gradient (u p)) z‖ ≤
          C * ‖y - z‖ ^ α := by
  obtain ⟨α, C, hα, hα1, hC, hh⟩ := compact_family_holder_of_local hK
    (fun p y => fderiv ℝ (gradient (u p)) y) hV.le
    (fun p y hy => hD2u p y (hKU hy) (hKr y hy).le) (by
      intro x hx
      obtain ⟨ρ, α, C, hρ, hα, hα1, hC, hh⟩ :=
        boundary_hessian_holder_near_regular_level hr hB x (hKr x hx) (hreg x hx)
          hU (hKU hx) hlam hV
      refine ⟨ρ, α, C, hρ, hα, hα1, hC, ?_⟩
      intro p y hy hxy z hz hxz
      simpa only [dist_eq_norm] using hh (u p) (f p) (hu p) (hf p)
        (hDu p) (hD2u p) (hpos p) (hA p) (hlo p) (hdf p) (hfne p) (hf1 p)
        (heq p) (hzero p) y hxy (hKr y hy) z hxz (hKr z hz))
  exact ⟨α, C, hα, hα1, hC, fun p y hy z hz => by
    simpa only [dist_eq_norm] using hh p y hy z hz⟩

end OAI.Analysis.PDE.Elliptic
