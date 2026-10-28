import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.Exponential

/-! # Continuous Holomorphic Log -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.ContinuousHolomorphicLog

noncomputable section

/-! A continuous logarithm of an actual holomorphic nonvanishing function is holomorphic. -/

open _root_.CategoryTheory _root_.TopologicalSpace Filter
open scoped _root_.Manifold ContDiff _root_.Topology

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {M : Type} [TopologicalSpace M] [ChartedSpace E M]

theorem continuous_logarithm_holomorphic
    (g : Holomorphic.Exponential.HolomorphicFunction (E := E) (M := M)) (l : C(M, ℂ))
    (hl : ∀ x, Complex.exp (l x) = g x) : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ) ∞ l := by
  intro p
  have hp : g p ≠ 0 := by rw [← hl p]; exact Complex.exp_ne_zero _
  let U := Holomorphic.Exponential.holomorphicLogarithmOpen g p
  let pU : U := ⟨p, Holomorphic.Exponential.mem_holomorphicLogarithmOpen g p hp⟩
  let L := Holomorphic.Exponential.holomorphicLocalLogarithm g p
  let r : C(U, ℂ) := l.comp ⟨Subtype.val, continuous_subtype_val⟩
  let s : C(U, ℂ) := ⟨L.val, L.property.continuous⟩
  have he (x : U) : Complex.exp (r x) * Complex.exp 0 = Complex.exp (s x) := by
    rw [Complex.exp_zero, mul_one]
    exact (hl x).trans (Holomorphic.Exponential.exp_holomorphicLocalLogarithm g p hp x).symm
  let n : U → ℤ := fun x => Logarithms.Construction.logarithmicDefect (r x) 0 (s x) (he x)
  have hn : IsLocallyConstant n := Logarithms.Construction.isLocallyConstant_logarithmicDefect r 0 s he
  have hlocal : ∀ᶠ x : U in 𝓝 pU,
      r x = s x + (n pU : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
    filter_upwards [hn.eventually_eq pU] with x hx
    have hd := Logarithms.Construction.logarithmicDefect_spec (r x) 0 (s x) (he x)
    change r x + 0 - s x = (n x : ℂ) * _ at hd
    rw [add_zero, hx] at hd
    exact sub_eq_iff_eq_add.mp hd |>.trans (add_comm _ _)
  apply (contMDiffAt_subtype_iff (U := U) (x := pU)).mp
  exact ((L.property pU).add contMDiffAt_const).congr_of_eventuallyEq hlocal

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.ContinuousHolomorphicLog
