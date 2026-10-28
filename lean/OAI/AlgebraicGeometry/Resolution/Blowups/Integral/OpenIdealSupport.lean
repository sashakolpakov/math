import OAI.AlgebraicGeometry.Resolution.Blowups.GlobalBlowup.Local

/-! # Open Ideal Support -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Integral.OpenIdealSupport.Construction

noncomputable section

/-! An ideal with open support on an integral scheme is zero or the unit ideal. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

theorem idealSheaf_eq_bot_or_top_of_isOpen_support
    {X : Scheme} [IsIntegral X] (I : X.IdealSheafData) (hopen : IsOpen (I.support : Set X)) :
    I = ⊥ ∨ I = ⊤ := by
  by_cases hzero : I = ⊥
  · exact Or.inl hzero
  right
  have hdense := GlobalBlowup.Local.Construction.idealSheaf_supportComplement_dense I hzero
  have hfull : (I.support.compl : Set X) = Set.univ :=
    hopen.isClosed_compl.closure_eq.symm.trans hdense.closure_eq
  apply (Scheme.IdealSheafData.support_eq_bot_iff I).mp
  apply SetLike.coe_injective
  apply Set.Subset.antisymm
  · intro x hx
    have hxc : x ∈ (I.support.compl : Set X) := hfull.symm ▸ Set.mem_univ x
    exact False.elim (hxc hx)
  · exact Set.empty_subset _

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Integral.OpenIdealSupport.Construction
