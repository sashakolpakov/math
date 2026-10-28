import OAI.AlgebraicGeometry.Divisors.LineBundles.RationalDivisorRestriction

/-! # Morphism Order Stalk -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.MorphismOrderStalk.BundleCycles

noncomputable section

/-!
# LineBundleCycles: rational orders along a morphism preserving the actual local data

The order is unchanged when the morphism identifies the function fields
and local rings and preserves the point's coheight. All maps are the
actual morphism-induced maps; the comparison follows from local quotient
lengths and their fraction-field extension.
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.Order

universe u

theorem ord_of_stalkMap_isIso {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (i : X ⟶ Y) (hη : i (genericPoint X) = genericPoint Y)
    [IsIso (Cycles.Functoriality.FunctionFields.Construction.genericFieldMap i hη)] (x : X) [IsIso (i.stalkMap x)]
    (hc : coheight (i x) = coheight x) (g : Y.functionField) :
    X.ord (Cycles.Functoriality.FunctionFields.Construction.genericFieldMap i hη g) x = Y.ord g (i x) := by
  by_cases hx : coheight x = 1
  · let : Ring.KrullDimLE 1 (X.presheaf.stalk x) := krullDimLE_of_coheight_le hx.le
    let : Ring.KrullDimLE 1 (Y.presheaf.stalk (i x)) := krullDimLE_of_coheight_le (hc.trans hx).le
    rw [Scheme.ord_eq_ordHom_of_coheight_eq_one hx, Scheme.ord_eq_ordHom_of_coheight_eq_one (hc.trans hx)]
    exact congrArg (fun z : WithZero (Multiplicative ℤ) => Multiplicative.toAdd (z.unzeroD 1))
      (RationalDivisorRestriction.BundleCycles.ringOrderFrac_equiv (asIso (i.stalkMap x)).commRingCatIsoToRingEquiv
        (asIso (Cycles.Functoriality.FunctionFields.Construction.genericFieldMap i hη)).commRingCatIsoToRingEquiv (RationalDivisorRestriction.BundleCycles.genericFieldMap_stalk i hη x) g)
  · rw [Scheme.ord_eq_zero_of_coheight_neq_one hx,
      Scheme.ord_eq_zero_of_coheight_neq_one (fun h => hx (hc.symm.trans h))]

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.MorphismOrderStalk.BundleCycles
