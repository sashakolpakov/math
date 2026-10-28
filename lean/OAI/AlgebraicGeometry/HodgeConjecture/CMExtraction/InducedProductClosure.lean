import Mathlib.Topology.Constructions.SumProd
import Mathlib.Topology.Maps.Basic

/-! # Induced Product Closure -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.InducedProductClosure.Approximation

/-! Approximation in the actual ambient away group transfers to the
rational away range with its induced topology. -/

variable {X A B G : Type*} [TopologicalSpace X] [TopologicalSpace A] [TopologicalSpace B]

theorem mem_closure_range_of_inducing_product (p : A → B) (hp : Topology.IsInducing p)
    (r : G → X × A) (x : X × A)
    (hx : Prod.map (id : X → X) p x ∈
      closure (Set.range (fun g => Prod.map (id : X → X) p (r g)))) :
    x ∈ closure (Set.range r) := by
  have hi : Topology.IsInducing (Prod.map (id : X → X) p) :=
    Topology.IsInducing.id.prodMap hp
  rw [hi.closure_eq_preimage_closure_image (Set.range r)]
  change Prod.map (id : X → X) p x ∈
    closure (Prod.map (id : X → X) p '' Set.range r)
  simpa only [← Set.range_comp, Function.comp_def] using hx

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.InducedProductClosure.Approximation
