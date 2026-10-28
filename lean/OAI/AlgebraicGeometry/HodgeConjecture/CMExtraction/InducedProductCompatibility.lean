import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.InducedProductClosure
import Mathlib.Topology.Algebra.Group.Basic

/-! # Induced Product Compatibility -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.InducedProductCompatibility.Approximation

/-! Transfer supported closure statements through a compatible induced
away embedding without expanding the specialized adelic group. -/

variable {X A B Γ : Type*} [Group X] [Group A] [Group B] [Group Γ]
  [TopologicalSpace X] [TopologicalSpace A] [TopologicalSpace B]
  (p : A →* B) (r : Γ →* X × A) (s : Γ →* X × B)
  (hcompat : ∀ g, Prod.map id p (r g) = s g)

include hcompat in
omit [TopologicalSpace X] [TopologicalSpace A] [TopologicalSpace B] in
theorem product_compatibility_first (g : Γ) : (r g).1 = (s g).1 :=
  congrArg Prod.fst (hcompat g)

include hcompat in
theorem compatible_induced_supported_closure (hp : Topology.IsInducing p)
    (x : X) (hx : (x, (1 : B)) ∈ closure (Set.range s)) :
    (x, (1 : A)) ∈ closure (Set.range r) := by
  apply InducedProductClosure.Approximation.mem_closure_range_of_inducing_product p hp r (x, 1)
  have hrange : Set.range (fun g => Prod.map id p (r g)) = Set.range s :=
    congrArg Set.range (funext hcompat)
  rw [hrange]
  simpa only [Prod.map_apply, id_eq, map_one] using hx

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.InducedProductCompatibility.Approximation
