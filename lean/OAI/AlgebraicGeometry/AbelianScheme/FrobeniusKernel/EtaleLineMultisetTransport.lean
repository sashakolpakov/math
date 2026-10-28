import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.OperatorSpecification

/-! # Etale Line Multiset Transport -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.EtaleLineMultisetTransport.Construction

noncomputable section

/-! Reindexing the etale-line correspondence preserves its multiset,
including multiplicities when distinct lines have the same target. -/

variable {q : ℕ} [Fact q.Prime] {X Y : Type}

theorem etaleLineMultiset_map (f : EtaleSubgroups.Construction.ActiveEtaleLine q → X) (g : X → Y) :
    (OperatorSpecification.Construction.etaleLineMultiset f).map g = OperatorSpecification.Construction.etaleLineMultiset (g ∘ f) := by
  exact Multiset.map_map g f _

theorem etaleLineMultiset_reindex (e : EtaleSubgroups.Construction.ActiveEtaleLine q ≃ EtaleSubgroups.Construction.ActiveEtaleLine q)
    (f : EtaleSubgroups.Construction.ActiveEtaleLine q → X) : OperatorSpecification.Construction.etaleLineMultiset (f ∘ e) = OperatorSpecification.Construction.etaleLineMultiset f := by
  let := Fintype.ofFinite (EtaleSubgroups.Construction.ActiveEtaleLine q)
  change (Finset.univ : Finset (EtaleSubgroups.Construction.ActiveEtaleLine q)).val.map (f ∘ e) = Finset.univ.val.map f
  rw [← Multiset.map_map, Multiset.map_univ_val_equiv]

theorem etaleLineMultiset_map_of_equiv (f : EtaleSubgroups.Construction.ActiveEtaleLine q → X)
    (g : EtaleSubgroups.Construction.ActiveEtaleLine q → Y) (h : X → Y)
    (e : EtaleSubgroups.Construction.ActiveEtaleLine q ≃ EtaleSubgroups.Construction.ActiveEtaleLine q) (he : ∀ L, h (f L) = g (e L)) :
    (OperatorSpecification.Construction.etaleLineMultiset f).map h = OperatorSpecification.Construction.etaleLineMultiset g := by
  have hf : h ∘ f = g ∘ e := funext he
  rw [etaleLineMultiset_map, hf, etaleLineMultiset_reindex]

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.EtaleLineMultisetTransport.Construction
