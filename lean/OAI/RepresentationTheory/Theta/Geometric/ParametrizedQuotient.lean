import Mathlib.Topology.Algebra.Group.Quotient

/-! # Parametrized Quotient -/

namespace OAI.RepresentationTheory.Theta.Geometric.ParametrizedQuotient

noncomputable section

/-! Continuous families of group maps descend through a fixed lattice
quotient, with their actual parameter and point formulas retained. -/

variable {B V X : Type} [AddCommGroup V]
    {G : B → Type} [∀ b, AddCommGroup (G b)]
    (Λ : AddSubgroup V) (f : ∀ b, V →+ G b) (hf : ∀ b, Λ ≤ (f b).ker)
    (embed : ∀ b, G b → X)

def parametrizedQuotientMap (p : B × (V ⧸ Λ)) : X :=
  embed p.1 (QuotientAddGroup.lift Λ (f p.1) (hf p.1) p.2)

theorem parametrizedQuotientMap_mk (b : B) (v : V) :
    parametrizedQuotientMap Λ f hf embed (b, QuotientAddGroup.mk v) = embed b (f b v) := rfl

theorem parametrizedQuotientMap_continuous
    [TopologicalSpace B] [TopologicalSpace V] [IsTopologicalAddGroup V] [TopologicalSpace X]
    (h : Continuous (fun p : B × V => embed p.1 (f p.1 p.2))) :
    Continuous (parametrizedQuotientMap Λ f hf embed) := by
  have hq : Topology.IsQuotientMap (Prod.map (id : B → B) (QuotientAddGroup.mk : V → V ⧸ Λ)) :=
    (IsOpenQuotientMap.id.prodMap QuotientAddGroup.isOpenQuotientMap_mk).isQuotientMap
  exact hq.continuous_iff.mpr h

end

end OAI.RepresentationTheory.Theta.Geometric.ParametrizedQuotient
