import OAI.AlgebraicGeometry.Divisors.LineBundles.FlatOrderEq
import Mathlib.AlgebraicGeometry.Morphisms.Flat

/-! # Flat Morphism Order -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.FlatMorphismOrder.BundleCycles

noncomputable section

/-!
# LineBundleCycles: native scheme orders at a reduced generic point of a flat fiber
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.Order

variable {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]

omit [IsLocallyNoetherian X] [IsLocallyNoetherian Y] in
theorem genericMorphism_stalkMap_injective (f : X ⟶ Y)
    (hη : f (genericPoint X) = genericPoint Y) (x : X) : Function.Injective (f.stalkMap x) := by
  intro a b hab
  apply IsFractionRing.injective (Y.presheaf.stalk (f x)) Y.functionField
  apply (Cycles.Functoriality.FunctionFields.Construction.genericFieldMap f hη).hom.injective
  rw [RationalDivisorRestriction.BundleCycles.genericFieldMap_stalk f hη x a, RationalDivisorRestriction.BundleCycles.genericFieldMap_stalk f hη x b]
  exact congrArg (algebraMap (X.presheaf.stalk x) X.functionField) hab

theorem ord_flat_stalk_eq (f : X ⟶ Y) [Flat f]
    (hη : f (genericPoint X) = genericPoint Y) (x : X)
    (hx : coheight x = 1) (hy : coheight (f x) = 1)
    (hmax : (IsLocalRing.maximalIdeal (Y.presheaf.stalk (f x))).map (f.stalkMap x).hom =
      IsLocalRing.maximalIdeal (X.presheaf.stalk x)) (g : Y.functionField) :
    X.ord (Cycles.Functoriality.FunctionFields.Construction.genericFieldMap f hη g) x = Y.ord g (f x) := by
  let R := Y.presheaf.stalk (f x)
  let S := X.presheaf.stalk x
  let : Algebra R S := (f.stalkMap x).hom.toAlgebra
  let : IsLocalHom (algebraMap R S) := inferInstanceAs (IsLocalHom (f.stalkMap x).hom)
  let : Module.Flat R S := Flat.stalkMap f x
  let : Ring.KrullDimLE 1 R := krullDimLE_of_coheight_le hy.le
  let : Ring.KrullDimLE 1 S := krullDimLE_of_coheight_le hx.le
  rw [Scheme.ord_eq_ordHom_of_coheight_eq_one hx, Scheme.ord_eq_ordHom_of_coheight_eq_one hy]
  exact congrArg WithZero.log (FlatOrderEq.BundleCycles.FlatOrder.ordFrac_eq R S hmax (genericMorphism_stalkMap_injective f hη x)
    (Cycles.Functoriality.FunctionFields.Construction.genericFieldMap f hη).hom (RationalDivisorRestriction.BundleCycles.genericFieldMap_stalk f hη x) g)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.FlatMorphismOrder.BundleCycles
