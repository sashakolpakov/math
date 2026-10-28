import OAI.AlgebraicGeometry.Divisors.LineBundles.Integral.FiberGenericPoint
import OAI.AlgebraicGeometry.Divisors.LineBundles.GenericFieldComposition

/-! # Fiber Field Naturality -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Integral.FiberFieldNaturality.BundleCycles

noncomputable section

section

/-! # LineBundleCycles: actual function-field pullback and fiber generic points on integral schemes -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace

variable {X Y : Scheme.{0}} (f : X ⟶ Y) [GeometricallyIntegral f]
    [IsIntegral X] [IsIntegral Y]

theorem integralFiberProjection_genericPoint : f (genericPoint X) = genericPoint Y := by
  apply Specializes.antisymm _ (genericPoint_specializes _ ) |>.eq
  obtain ⟨x, hx⟩ := (inferInstance : Surjective f).surj (genericPoint Y)
  exact hx ▸ (genericPoint_specializes x).map f.continuous

theorem integralFiberGenericPoint_generic :
    FiberGenericPoint.BundleCycles.integralFiberGenericPoint f (genericPoint Y) = genericPoint X := by
  apply Eq.symm
  apply FiberGenericPoint.BundleCycles.integralFiberGenericPoint_unique f _ _ (integralFiberProjection_genericPoint f)
  intro z _
  exact genericPoint_specializes z

def integralFiberFunctionFieldMap : Y.functionField ⟶ X.functionField :=
  Cycles.Functoriality.FunctionFields.Construction.genericFieldMap f (integralFiberProjection_genericPoint f)

theorem integralFiberFunctionFieldMap_ne_zero (g : Y.functionField) (hg : g ≠ 0) :
    integralFiberFunctionFieldMap f g ≠ 0 :=
  (map_ne_zero_iff _ (integralFiberFunctionFieldMap f).hom.injective).mpr hg

end

/-! # LineBundleCycles: actual generic-stalk maps on open squares and isomorphic factorizations -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

theorem integralFiberFunctionFieldMap_iso {X Y S : Scheme.{0}}
    [IsIntegral X] [IsIntegral Y] [IsIntegral S]
    (e : X ≅ Y) (p : X ⟶ S) (q : Y ⟶ S)
    [GeometricallyIntegral p] [GeometricallyIntegral q] (h : e.hom ≫ q = p) :
    integralFiberFunctionFieldMap p = integralFiberFunctionFieldMap q ≫ RationalDivisorRestriction.BundleCycles.openFunctionFieldMap e.hom :=
  (GenericFieldComposition.BundleCycles.genericFieldMap_congr h.symm _ _).trans
    (GenericFieldComposition.BundleCycles.genericFieldMap_comp e.hom q (genericPoint_eq_of_isOpenImmersion e.hom)
      (integralFiberProjection_genericPoint q))

theorem integralFiberFunctionFieldMap_openSquare {X Y X' Y' : Scheme.{0}}
    [IsIntegral X] [IsIntegral Y] [IsIntegral X'] [IsIntegral Y']
    (p : X ⟶ Y) (q : X' ⟶ Y') [GeometricallyIntegral p] [GeometricallyIntegral q]
    (i : Y' ⟶ Y) (j : X' ⟶ X) [IsOpenImmersion i] [IsOpenImmersion j]
    (h : j ≫ p = q ≫ i) :
    integralFiberFunctionFieldMap p ≫ RationalDivisorRestriction.BundleCycles.openFunctionFieldMap j =
      RationalDivisorRestriction.BundleCycles.openFunctionFieldMap i ≫ integralFiberFunctionFieldMap q :=
  (GenericFieldComposition.BundleCycles.genericFieldMap_comp j p (genericPoint_eq_of_isOpenImmersion j)
    (integralFiberProjection_genericPoint p)).symm.trans
      ((GenericFieldComposition.BundleCycles.genericFieldMap_congr h _ _).trans
        (GenericFieldComposition.BundleCycles.genericFieldMap_comp q i (integralFiberProjection_genericPoint q)
          (genericPoint_eq_of_isOpenImmersion i)))

theorem integralFiberFunctionFieldMap_factorization {X W Y S : Scheme.{0}}
    [IsIntegral X] [IsIntegral W] [IsIntegral Y] [IsIntegral S]
    (e : X ≅ W) (p : X ⟶ S) (f : W ⟶ Y) (g : Y ⟶ S)
    [GeometricallyIntegral p] [GeometricallyIntegral f] [GeometricallyIntegral g]
    (h : e.hom ≫ f ≫ g = p) :
    integralFiberFunctionFieldMap p ≫ RationalDivisorRestriction.BundleCycles.openFunctionFieldMap e.inv =
      integralFiberFunctionFieldMap g ≫ integralFiberFunctionFieldMap f := by
  have hi : e.inv ≫ p = f ≫ g := by
    rw [← h, ← Category.assoc, e.inv_hom_id, Category.id_comp]
  exact (GenericFieldComposition.BundleCycles.genericFieldMap_comp e.inv p (genericPoint_eq_of_isOpenImmersion e.inv)
    (integralFiberProjection_genericPoint p)).symm.trans
      ((GenericFieldComposition.BundleCycles.genericFieldMap_congr hi _ _).trans
        (GenericFieldComposition.BundleCycles.genericFieldMap_comp f g (integralFiberProjection_genericPoint f)
          (integralFiberProjection_genericPoint g)))

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Integral.FiberFieldNaturality.BundleCycles
