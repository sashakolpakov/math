import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Affine.DivisorNorm
import OAI.AlgebraicGeometry.Cycles.Functoriality.FunctionFields

/-! # Divisor Restriction -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Divisor.DivisorRestriction

noncomputable section

/-! Principal divisors of arbitrary rational functions commute with open
restriction. The comparison uses the actual stalk maps, including negative
orders, and is needed to pass the finite affine norm formula to scheme charts. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.Order

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Affine.DivisorNorm

universe u

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]

theorem genericFieldMap_stalk (i : X ⟶ Y)
    (hη : i (genericPoint X) = genericPoint Y) (x : X)
    (a : Y.presheaf.stalk (i x)) :
    Cycles.Functoriality.FunctionFields.Construction.genericFieldMap i hη (algebraMap (Y.presheaf.stalk (i x)) Y.functionField a) =
      algebraMap (X.presheaf.stalk x) X.functionField (i.stalkMap x a) := by
  have h : CommRingCat.ofHom (algebraMap (Y.presheaf.stalk (i x)) Y.functionField) ≫
      Cycles.Functoriality.FunctionFields.Construction.genericFieldMap i hη = i.stalkMap x ≫
        CommRingCat.ofHom (algebraMap (X.presheaf.stalk x) X.functionField) := by
    change Y.presheaf.stalkSpecializes ((genericPoint_spec Y).specializes trivial) ≫
      Cycles.Functoriality.FunctionFields.Construction.genericFieldMap i hη = i.stalkMap x ≫
        X.presheaf.stalkSpecializes ((genericPoint_spec X).specializes trivial)
    rw [Cycles.Functoriality.FunctionFields.Construction.genericFieldMap, TopCat.Presheaf.stalkCongr_hom,
      ← Category.assoc, TopCat.Presheaf.stalkSpecializes_comp]
    exact i.stalkSpecializes_stalkMap (genericPoint X) x
      ((genericPoint_spec X).specializes trivial)
  exact congrArg (fun k : Y.presheaf.stalk (i x) ⟶ X.functionField => k a) h

variable (i : X ⟶ Y) [IsOpenImmersion i]

def openFieldMap : Y.functionField ⟶ X.functionField :=
  Cycles.Functoriality.FunctionFields.Construction.genericFieldMap i (genericPoint_eq_of_isOpenImmersion i)

instance : IsIso (openFieldMap i) := by
  unfold openFieldMap Cycles.Functoriality.FunctionFields.Construction.genericFieldMap
  infer_instance

def openFieldIso : Y.functionField ≅ X.functionField := asIso (openFieldMap i)

theorem openFieldMap_stalk (x : X) (a : Y.presheaf.stalk (i x)) :
    openFieldMap i (algebraMap (Y.presheaf.stalk (i x)) Y.functionField a) =
      algebraMap (X.presheaf.stalk x) X.functionField (i.stalkMap x a) :=
  genericFieldMap_stalk i (genericPoint_eq_of_isOpenImmersion i) x a

variable [IsLocallyNoetherian X] [IsLocallyNoetherian Y]

/-- Every integer order, including a pole, is preserved on an open chart. -/
theorem ord_openImmersion (f : Y.functionField) (x : X) :
    X.ord (openFieldMap i f) x = Y.ord f (i x) := by
  have hc : coheight (i x) = coheight x := coheight_eq_of_isOpenImmersion i
  by_cases hx : coheight x = 1
  · let : Ring.KrullDimLE 1 (X.presheaf.stalk x) := krullDimLE_of_coheight_le hx.le
    let : Ring.KrullDimLE 1 (Y.presheaf.stalk (i x)) :=
      krullDimLE_of_coheight_le (hc.trans hx).le
    rw [Scheme.ord_eq_ordHom_of_coheight_eq_one hx,
      Scheme.ord_eq_ordHom_of_coheight_eq_one (hc.trans hx)]
    exact congrArg WithZero.log (OrderQuotientTransport.ordFrac_equiv
      (asIso (i.stalkMap x)).commRingCatIsoToRingEquiv
      (openFieldIso i).commRingCatIsoToRingEquiv (openFieldMap_stalk i x) f)
  · rw [Scheme.ord_eq_zero_of_coheight_neq_one hx,
      Scheme.ord_eq_zero_of_coheight_neq_one (fun h => hx (hc.symm.trans h))]

variable [AlgebraicGeometry.IsNoetherian X] [AlgebraicGeometry.IsNoetherian Y]

omit [IsLocallyNoetherian X] [IsLocallyNoetherian Y] in
theorem principalDivisor_openImmersion (f : Y.functionField) :
    Finsupp.comapDomain i (Divisors.LineBundles.Ord.BundleCycles.principalDivisor Y f) i.isOpenEmbedding.injective.injOn =
      Divisors.LineBundles.Ord.BundleCycles.principalDivisor X (openFieldMap i f) := by
  ext x
  exact (ord_openImmersion i f x).symm

omit [IsLocallyNoetherian X] [IsLocallyNoetherian Y] in
theorem rationalPrincipalDivisor_openImmersion (f : Y.functionField) :
    Finsupp.comapDomain i (Affine.DivisorNorm.rationalPrincipalDivisor Y f) i.isOpenEmbedding.injective.injOn =
      Affine.DivisorNorm.rationalPrincipalDivisor X (openFieldMap i f) := by
  ext x
  exact congrArg (fun n : ℤ => (n : ℚ)) (ord_openImmersion i f x).symm

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Divisor.DivisorRestriction
