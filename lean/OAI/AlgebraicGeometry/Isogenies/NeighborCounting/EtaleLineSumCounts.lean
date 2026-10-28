import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Parameter.MultisetEnumeration
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.EtaleLineMultisetTransport

/-! # Etale Line Sum Counts -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.EtaleLineSumCounts

noncomputable section

/-! The literal dimension-one submodule sum is the native etale-line
multiset; every actual line reindexing retains repeated target values. -/

open scoped BigOperators

open OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.EtaleLineMultisetTransport.Construction OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Parameter.MultisetEnumeration

variable {q : ℕ} [Fact q.Prime] {X : Type}
local instance : Fintype (Submodule (ZMod q) (AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.ActiveEtalePlane q)) := Fintype.ofFinite _

open Classical in
theorem line_sum_eq_etaleLineMultiset (f : Submodule (ZMod q) (AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.ActiveEtalePlane q) → X) :
    (∑ U : Submodule (ZMod q) (AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.ActiveEtalePlane q),
      if Module.finrank (ZMod q) U = 1 then ({f U} : Multiset X) else 0) =
        AbelianScheme.FrobeniusKernel.OperatorSpecification.Construction.etaleLineMultiset (fun J : AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.ActiveEtaleLine q => f J.val) := by
  let := Fintype.ofFinite (AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.ActiveEtaleLine q)
  have h := Parameter.MultisetEnumeration.parameter_multiset_subtype
    (fun U : Submodule (ZMod q) (AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.ActiveEtalePlane q) => Module.finrank (ZMod q) U = 1)
    (Equiv.refl (AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.ActiveEtaleLine q)) (fun J : AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.ActiveEtaleLine q => f J.val)
  change (Finset.univ : Finset (AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.ActiveEtaleLine q)).val.map (fun J => f J.val) =
    (∑ U : Submodule (ZMod q) (AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.ActiveEtalePlane q),
      if Module.finrank (ZMod q) U = 1 then ({f U} : Multiset X) else 0) at h
  exact h.symm

open Classical in
theorem line_sum_eq_of_equiv (f : Submodule (ZMod q) (AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.ActiveEtalePlane q) → X)
    (g : AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.ActiveEtaleLine q → X) (e : AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.ActiveEtaleLine q ≃ AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.ActiveEtaleLine q)
    (h : ∀ J : AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.ActiveEtaleLine q, f J.val = g (e J)) :
    (∑ U : Submodule (ZMod q) (AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.ActiveEtalePlane q),
      if Module.finrank (ZMod q) U = 1 then ({f U} : Multiset X) else 0) = AbelianScheme.FrobeniusKernel.OperatorSpecification.Construction.etaleLineMultiset g := by
  have hf : (fun J : AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.ActiveEtaleLine q => f J.val) = g ∘ e := funext h
  rw [line_sum_eq_etaleLineMultiset, hf, AbelianScheme.FrobeniusKernel.EtaleLineMultisetTransport.Construction.etaleLineMultiset_reindex]

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.EtaleLineSumCounts
