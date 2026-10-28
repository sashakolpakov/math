import OAI.AlgebraicGeometry.Divisors.LineBundles.FunctionFieldUnitGerm
import OAI.AlgebraicGeometry.Divisors.LineBundles.GenericFieldComposition
import OAI.AlgebraicGeometry.Divisors.LineBundles.RationalDivisorRestriction

/-! # Function Field Units -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Open.FunctionFieldUnits.BundleCycles

noncomputable section

/-! # LineBundleCycles: actual open-immersion pullback of unit-valued rational functions and regular germs -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y] (i : Y ⟶ X) [IsOpenImmersion i]

def openFunctionFieldUnits : X.functionFieldˣ →* Y.functionFieldˣ :=
  Units.map (RationalDivisorRestriction.BundleCycles.openFunctionFieldMap i).hom.toMonoidHom

instance openImage_nonempty (W : Y.Opens) [Nonempty W] : Nonempty (i ''ᵁ W) := by
  obtain ⟨w⟩ := ‹Nonempty W›
  exact ⟨⟨i w.val, w.val, w.property, rfl⟩⟩

theorem openFunctionFieldUnits_germ (W : Y.Opens) [Nonempty W] (a : Γ(X, i ''ᵁ W)ˣ) :
    openFunctionFieldUnits i (FunctionFieldUnitGerm.BundleCycles.functionFieldUnitGerm (i ''ᵁ W) a) =
      FunctionFieldUnitGerm.BundleCycles.functionFieldUnitGerm W (Units.map (i.appIso W).hom.hom.toMonoidHom a) := by
  apply Units.ext
  change RationalDivisorRestriction.BundleCycles.openFunctionFieldMap i (X.germToFunctionField (i ''ᵁ W) a.val) =
    Y.germToFunctionField W ((i.appIso W).hom a.val)
  rw [Scheme.Hom.appIso_hom']
  exact ConcreteCategory.congr_hom
    (GenericFieldComposition.BundleCycles.genericFieldMap_germ_appLE i (genericPoint_eq_of_isOpenImmersion i)
      (i ''ᵁ W) W (i.preimage_image_eq W).ge) a.val

theorem openFunctionFieldUnits_order [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (a : X.functionFieldˣ) (x : Y) : Y.ord (openFunctionFieldUnits i a).val x = X.ord a.val (i x) :=
  RationalDivisorRestriction.BundleCycles.ord_openImmersion i a.val x

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Open.FunctionFieldUnits.BundleCycles
