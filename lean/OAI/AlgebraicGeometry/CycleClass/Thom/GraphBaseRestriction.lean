import Mathlib.Topology.LocalAtTarget
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Sets.Opens

/-! # Graph Base Restriction -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.GraphBaseRestriction.Constructions

noncomputable section

/-! Restricting an actual graph over a base open preserves its closed embedding into the corresponding product. -/

open _root_.TopologicalSpace

variable {X N F : Type*} [TopologicalSpace X] [TopologicalSpace N] [TopologicalSpace F]

def baseProductHomeomorph (U : Set N) : (Prod.fst ⁻¹' U : Set (N × F)) ≃ₜ (U × F) where
  toFun z := (⟨z.val.1, z.property⟩, z.val.2)
  invFun z := ⟨(z.1.val, z.2), z.1.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := ((continuous_fst.comp continuous_subtype_val).subtype_mk _).prodMk
    (continuous_snd.comp continuous_subtype_val)
  continuous_invFun := ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd).subtype_mk _

def restrictedGraph (g : X → N) (e : X → F) (U : Set N) : (g ⁻¹' U) → (U × F) :=
  fun z => (⟨g z.val, z.property⟩, e z.val)

theorem restrictedGraph_closedEmbedding (g : X → N) (e : X → F) (U : Set N)
    (h : Topology.IsClosedEmbedding (fun x => (g x, e x))) :
    Topology.IsClosedEmbedding (restrictedGraph g e U) :=
  (baseProductHomeomorph (F := F) U).isClosedEmbedding.comp
    (h.restrictPreimage (Prod.fst ⁻¹' U : Set (N × F)))

omit [TopologicalSpace X] [TopologicalSpace N] [TopologicalSpace F] in
theorem restrictedGraph_bound (g : X → N) (e : X → F) (U : Set N) (K : Set F)
    (hK : ∀ x, g x ∈ U → e x ∈ K) :
    Set.range (restrictedGraph g e U) ⊆ Set.univ ×ˢ K := by
  rintro z ⟨x, rfl⟩
  exact ⟨trivial, hK x.val x.property⟩

end

end OAI.AlgebraicGeometry.CycleClass.Thom.GraphBaseRestriction.Constructions
