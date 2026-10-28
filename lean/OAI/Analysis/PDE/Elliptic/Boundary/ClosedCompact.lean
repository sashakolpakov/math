import OAI.Analysis.PDE.Elliptic.Boundary.ClosedPhysical
import OAI.Analysis.PDE.Elliptic.Boundary.InteriorNeighborhood
import OAI.Analysis.PDE.Elliptic.Boundary.CompactHolder

/-! Uniform full Hessian Hölder control on arbitrary compact portions of
the closed domain, for families of actual nonlinear Dirichlet solutions. -/

noncomputable section
namespace OAI.Analysis.PDE.Elliptic

open Set InnerProductSpace OAI.Analysis.PDE.Dirichlet OAI.Analysis.Calculus.Quaternion OAI.LinearAlgebra.Moore
open scoped Topology Matrix ComplexOrder

theorem closed_hessian_holder_on_compact {n : ℕ}
    {P : Type*} {r B : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n + 1) 4 → ℝ}
    (hr : ContDiff ℝ 3 r) (hB : ContDiff ℝ 3 B)
    {U K : Set (OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n + 1) 4)} (hU : IsOpen U) (hK : IsCompact K)
    (hKU : K ⊆ U) (hKr : ∀ x ∈ K, r x ≤ 0)
    (hreg : ∀ x ∈ K, r x = 0 → fderiv ℝ r x ≠ 0)
    {lam V L₁ L₂ : ℝ} (hlam : 0 < lam) (hV : 0 < V) (hLV : lam ≤ V)
    (hL₁ : 0 ≤ L₁) (hL₂ : 0 ≤ L₂)
    (u f : P → OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n + 1) 4 → ℝ)
    (hu : ∀ p, ContDiff ℝ 4 (u p)) (hf : ∀ p, Continuous (f p))
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
      OAI.LinearAlgebra.Moore.mooreDet (n + 1) (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (u p) y) = f p y)
    (hlog : ∀ p y, y ∈ U ∩ {z | r z < 0} → ∀ z, z ∈ U ∩ {z | r z < 0} →
      |Real.log (f p y) - Real.log (f p z)| ≤ L₁ * dist y z)
    (hlog₂ : ∀ p y, y ∈ U ∩ {z | r z < 0} → ∀ v,
      -L₂ * ‖v‖ ^ 2 ≤ deriv (deriv (fun t : ℝ => Real.log (f p (y + t • v)))) 0)
    (hzero : ∀ p y, y ∈ U → r y = 0 → u p y = B y) :
    ∃ α C : ℝ, 0 < α ∧ α < 1 ∧ 0 < C ∧
      ∀ p y, y ∈ K → ∀ z, z ∈ K →
        ‖fderiv ℝ (gradient (u p)) y - fderiv ℝ (gradient (u p)) z‖ ≤
          C * ‖y - z‖ ^ α := by
  have hell (p) (y) (hy : y ∈ U ∩ {z | r z < 0}) (w : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n + 1) 4) :
      lam * ‖w‖ ^ 2 ≤ OAI.Analysis.PDE.Dirichlet.logPrincipalSymbol (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (u p) y) w ∧
      OAI.Analysis.PDE.Dirichlet.logPrincipalSymbol (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (u p) y) w ≤ V * ‖w‖ ^ 2 := by
    rw [← OAI.Analysis.PDE.Dirichlet.logRealOperator_symbol]
    refine ⟨hlo p y hy.1 hy.2.le w, ?_⟩
    apply (real_inner_le_norm _ _).trans
    have hh := (OAI.Analysis.PDE.Dirichlet.logRealOperator (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (u p) y)).le_opNorm w
    have hh' := hh.trans (mul_le_mul_of_nonneg_right (hA p y hy.1 hy.2.le) (norm_nonneg w))
    nlinarith [mul_le_mul_of_nonneg_left hh' (norm_nonneg w)]
  obtain ⟨α, C, hα, hα1, hC, hh⟩ := compact_family_holder_of_local hK
    (fun p y => fderiv ℝ (gradient (u p)) y) hV.le
    (fun p y hy => hD2u p y (hKU hy) (hKr y hy)) (by
      intro x hx
      by_cases hrx : r x = 0
      · obtain ⟨ρ, α, C, hρ, hα, hα1, hC, hh⟩ :=
          closed_hessian_holder_near_regular_level hr hB x hrx (hreg x hx hrx)
            hU (hKU hx) hlam hV hLV hL₁ hL₂
        refine ⟨ρ, α, C, hρ, hα, hα1, hC, ?_⟩
        intro p y hy hxy z hz hxz
        simpa only [dist_eq_norm] using hh (u p) (f p) (hu p) (hf p)
          (hDu p) (hD2u p) (hpos p) (hA p) (hlo p) (hdf p) (hfne p) (hf1 p)
          (heq p) (hlog p) (hlog₂ p) (hzero p) y hxy (hKr y hy) z hxz (hKr z hz)
      · have hrx' : r x < 0 := lt_of_le_of_ne (hKr x hx) hrx
        obtain ⟨ρ, α, C, hρ, hα, hα1, hC, hh⟩ :=
          interior_hessian_holder_near_point
            (hU.inter (isOpen_lt hr.continuous continuous_const)) x ⟨hKU hx, hrx'⟩
            hlam hLV hL₁ hL₂ hV.le
        refine ⟨ρ, α, C, hρ, hα, hα1, hC, ?_⟩
        intro p y hy hxy z hz hxz
        exact hh (u p) (f p) (hu p)
          (fun y hy => hpos p y hy.1 hy.2.le)
          (fun y hy => heq p y hy.1 hy.2)
          (hell p) (fun y hy => hD2u p y hy.1 hy.2.le)
          (hlog p) (hlog₂ p) y hxy z hxz)
  exact ⟨α, C, hα, hα1, hC, fun p y hy z hz => by
    simpa only [dist_eq_norm] using hh p y hy z hz⟩

end OAI.Analysis.PDE.Elliptic
