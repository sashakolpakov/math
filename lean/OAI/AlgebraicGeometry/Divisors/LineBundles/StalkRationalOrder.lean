import OAI.AlgebraicGeometry.Divisors.LineBundles.StalkLocalization
import OAI.AlgebraicGeometry.Divisors.LineBundles.MorphismOrderStalk

/-! # Stalk Rational Order -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.StalkRationalOrder.BundleCycles

noncomputable section

/-!
# LineBundleCycles: actual rational functions and complete divisors on a stalk spectrum
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.Order

universe u

variable (X : Scheme.{u}) [IsIntegral X] (x : X)

def stalkFunctionFieldMap : X.functionField ⟶ (Spec (X.presheaf.stalk x)).functionField :=
  Cycles.Functoriality.FunctionFields.Construction.genericFieldMap (X.fromSpecStalk x) (StalkLocalization.BundleCycles.fromSpecStalk_genericPoint X x)

instance stalkFunctionFieldMap_isIso : IsIso (stalkFunctionFieldMap X x) := by
  let p := genericPoint (Spec (X.presheaf.stalk x))
  let e := X.presheaf.stalkCongr (Inseparable.of_eq (StalkLocalization.BundleCycles.fromSpecStalk_genericPoint X x).symm)
  exact (e ≪≫ (@asIso _ _ _ _ _ (StalkLocalization.BundleCycles.fromSpecStalk_stalkMap_isIso X x p))).isIso_hom

section LocalOrder

variable [IsLocallyNoetherian X]

theorem ord_fromSpecStalk (g : X.functionField) (p : Spec (X.presheaf.stalk x)) :
    (Spec (X.presheaf.stalk x)).ord (stalkFunctionFieldMap X x g) p =
      X.ord g (X.fromSpecStalk x p) := by
  let : IsIso ((X.fromSpecStalk x).stalkMap p) := StalkLocalization.BundleCycles.fromSpecStalk_stalkMap_isIso X x p
  let : IsIso (Cycles.Functoriality.FunctionFields.Construction.genericFieldMap (X.fromSpecStalk x) (StalkLocalization.BundleCycles.fromSpecStalk_genericPoint X x)) :=
    stalkFunctionFieldMap_isIso X x
  exact MorphismOrderStalk.BundleCycles.ord_of_stalkMap_isIso (X.fromSpecStalk x) (StalkLocalization.BundleCycles.fromSpecStalk_genericPoint X x) p
    (StalkLocalization.BundleCycles.fromSpecStalk_coheight X x p) g

end LocalOrder

variable [AlgebraicGeometry.IsNoetherian X]

theorem principalDivisor_fromSpecStalk (g : X.functionField) :
    Finsupp.comapDomain (X.fromSpecStalk x) (Ord.BundleCycles.principalDivisor X g)
      (X.fromSpecStalk x).isEmbedding.injective.injOn =
      Ord.BundleCycles.principalDivisor (Spec (X.presheaf.stalk x)) (stalkFunctionFieldMap X x g) := by
  ext p
  exact (ord_fromSpecStalk X x g p).symm

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.StalkRationalOrder.BundleCycles
