import Mathlib.Analysis.Calculus.FDeriv.Congr
import Mathlib.Analysis.Complex.Basic

/-! # Gluing -/

namespace OAI.RepresentationTheory.Theta.Geometric.Holomorphic.Gluing

noncomputable section

/-! Holomorphic scalar functions glue over an actual open cover. -/

open scoped _root_.Topology

theorem exists_differentiable_gluing {V ι : Type*}
    [NormedAddCommGroup V] [NormedSpace ℂ V]
    (U : ι → Set V) (C : ι → V → ℂ)
    (hopen : ∀ i, IsOpen (U i)) (hcover : ∀ x, ∃ i, x ∈ U i)
    (hdiff : ∀ i x, x ∈ U i → DifferentiableAt ℂ (C i) x)
    (hcompat : ∀ i j x, x ∈ U i → x ∈ U j → C i x = C j x) :
    ∃ c : V → ℂ, Differentiable ℂ c ∧ ∀ i x, x ∈ U i → c x = C i x := by
  choose k hk using hcover
  let c := fun x => C (k x) x
  have hmatch : ∀ i x, x ∈ U i → c x = C i x := by
    intro i x hx
    exact hcompat (k x) i x (hk x) hx
  refine ⟨c, ?_, hmatch⟩
  intro x
  apply (hdiff (k x) x (hk x)).congr_of_eventuallyEq
  filter_upwards [(hopen (k x)).mem_nhds (hk x)] with y hy
  exact hmatch (k x) y hy

end

end OAI.RepresentationTheory.Theta.Geometric.Holomorphic.Gluing
