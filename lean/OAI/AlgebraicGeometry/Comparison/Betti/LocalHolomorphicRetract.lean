import OAI.AlgebraicGeometry.Comparison.Betti.LocalHolomorphicComposition

/-! # Local Holomorphic Retract -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.LocalHolomorphicRetract.Analytic

noncomputable section

/-! A local holomorphic left inverse makes the original pullback of holomorphic germs surjective. -/

open Set Filter
open scoped _root_.Topology ContDiff

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

theorem localHolomorphicComposition_surjective_of_leftInverse (f : E → F) (x : E)
    (hf : ContDiffAt ℂ ω f x) (g : F → E) (hg : ContDiffAt ℂ ω g (f x))
    (hgf : (fun z => g (f z)) =ᶠ[𝓝 x] id) :
    Function.Surjective (LocalHolomorphicComposition.Analytic.localHolomorphicComposition f x hf) := by
  have hx : g (f x) = x := hgf.eq_of_nhds
  intro a
  refine ⟨LocalHolomorphicComposition.Analytic.localHolomorphicCompositionAt g (f x) hg x hx a, ?_⟩
  obtain ⟨v, hva, _⟩ := a.property
  apply Subtype.ext
  rw [LocalHolomorphicComposition.Analytic.localHolomorphicComposition_val, LocalHolomorphicComposition.Analytic.localHolomorphicCompositionAt_val, ← hva]
  apply Germ.coe_eq.mpr
  filter_upwards [hgf] with z hz
  exact congrArg v hz

theorem localHolomorphicCompositionAt_surjective_of_leftInverse (f : E → F) (x : E)
    (hf : ContDiffAt ℂ ω f x) (y : F) (hxy : f x = y)
    (g : F → E) (hg : ContDiffAt ℂ ω g y)
    (hgf : (fun z => g (f z)) =ᶠ[𝓝 x] id) :
    Function.Surjective (LocalHolomorphicComposition.Analytic.localHolomorphicCompositionAt f x hf y hxy) := by
  subst y
  exact localHolomorphicComposition_surjective_of_leftInverse f x hf g hg hgf

end

end OAI.AlgebraicGeometry.Comparison.Betti.LocalHolomorphicRetract.Analytic
