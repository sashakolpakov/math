import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Divisor.DivisorRestriction

/-! # Stalk Iso -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Divisor.StalkIso

noncomputable section

/-! Local orders are invariant under a morphism that preserves the local
ring, the function field, and the point's codimension. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.Order

universe u

theorem ord_eq_of_stalkMap_isIso {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (i : X ⟶ Y) (hη : i (genericPoint X) = genericPoint Y)
    [IsIso (Cycles.Functoriality.FunctionFields.Construction.genericFieldMap i hη)] (x : X) [IsIso (i.stalkMap x)]
    (hc : coheight (i x) = coheight x) (f : Y.functionField) :
    X.ord (Cycles.Functoriality.FunctionFields.Construction.genericFieldMap i hη f) x = Y.ord f (i x) := by
  by_cases hx : coheight x = 1
  · let : Ring.KrullDimLE 1 (X.presheaf.stalk x) := krullDimLE_of_coheight_le hx.le
    let : Ring.KrullDimLE 1 (Y.presheaf.stalk (i x)) :=
      krullDimLE_of_coheight_le (hc.trans hx).le
    rw [Scheme.ord_eq_ordHom_of_coheight_eq_one hx,
      Scheme.ord_eq_ordHom_of_coheight_eq_one (hc.trans hx)]
    exact congrArg WithZero.log (OrderQuotientTransport.ordFrac_equiv
      (asIso (i.stalkMap x)).commRingCatIsoToRingEquiv
      (asIso (Cycles.Functoriality.FunctionFields.Construction.genericFieldMap i hη)).commRingCatIsoToRingEquiv
      (DivisorRestriction.genericFieldMap_stalk i hη x) f)
  · rw [Scheme.ord_eq_zero_of_coheight_neq_one hx,
      Scheme.ord_eq_zero_of_coheight_neq_one (fun h => hx (hc.symm.trans h))]

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Divisor.StalkIso
