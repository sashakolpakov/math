import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Normalization.StalkMap
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.NormalizedStalkDivisor
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Generic.Fields

/-! # Stalk Fields -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Normalization.StalkFields

noncomputable section

/-! The normalized-stalk and global-normalization constructions carry the
same rational function. Compatibility is checked on an affine chart's
sections and extended through its actual fraction field. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Normalization.Scheme OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Normalization.Fields OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Normalization.StalkMap

universe u

local instance (A : Type u) [CommRing A] [IsDomain A] :
    Algebra A (Spec (.of A)).functionField :=
  (StructureSheaf.toStalk A (genericPoint (Spec (.of A)))).hom.toAlgebra

variable (X : Scheme.{u}) [IsIntegral X]
  (U : X.Opens) (hU : IsAffineOpen U) [Nonempty U] (x : U)

omit [IsIntegral X] [Nonempty U] in
theorem fromSpecStalk_preimage : X.fromSpecStalk x ⁻¹ᵁ U = ⊤ :=
  Scheme.preimage_eq_top_of_closedPoint_mem (X.fromSpecStalk x)
    (by simpa only [Scheme.fromSpecStalk_closedPoint] using x.property)

omit [IsIntegral X] [Nonempty U] in
theorem fromSpecStalk_appLE :
    (X.fromSpecStalk x).appLE U ⊤ (le_of_eq (fromSpecStalk_preimage X U x).symm) =
      X.presheaf.germ U x x.property ≫ (Scheme.ΓSpecIso (X.presheaf.stalk x)).inv := by
  rw [Scheme.Hom.appLE, Scheme.fromSpecStalk_app x.property]
  have he (a : Opposite.op (⊤ : (Spec (X.presheaf.stalk x)).Opens) ⟶
      Opposite.op (⊤ : (Spec (X.presheaf.stalk x)).Opens)) : a = 𝟙 _ :=
    Subsingleton.elim _ _
  simp only [Category.assoc, ← Functor.map_comp, he]
  rw [(Spec (X.presheaf.stalk x)).presheaf.map_id, Category.comp_id]

def stalkBaseMap :
    Spec (.of (integralClosure (X.presheaf.stalk x) X.functionField)) ⟶ X :=
  Spec.map (CommRingCat.ofHom (algebraMap (X.presheaf.stalk x)
    (integralClosure (X.presheaf.stalk x) X.functionField))) ≫ X.fromSpecStalk x

omit [Nonempty U] in
theorem stalkBaseMap_preimage : stalkBaseMap X U x ⁻¹ᵁ U = ⊤ := by
  rw [stalkBaseMap, Scheme.Hom.comp_preimage, fromSpecStalk_preimage, TopologicalSpace.Opens.map_top]

include hU in
theorem stalkBaseMap_genericPoint :
    stalkBaseMap X U x
      (genericPoint (Spec (.of (integralClosure (X.presheaf.stalk x) X.functionField)))) =
        genericPoint X := by
  change (Spec.map _ ≫ X.fromSpecStalk x) _ = _
  rw [← StalkMap.normalizationStalkMap_comp X U hU x, Scheme.Hom.comp_apply,
    StalkMap.normalizationStalkMap_genericPoint, Fields.normalizationMap_genericPoint]

omit [Nonempty U] in
theorem stalkBaseMap_appLE :
    (stalkBaseMap X U x).appLE U ⊤ (le_of_eq (stalkBaseMap_preimage X U x).symm) =
      X.presheaf.germ U x x.property ≫
        CommRingCat.ofHom (algebraMap (X.presheaf.stalk x)
          (integralClosure (X.presheaf.stalk x) X.functionField)) ≫
        (Scheme.ΓSpecIso (.of (integralClosure (X.presheaf.stalk x) X.functionField))).inv := by
  let j := Spec.map (CommRingCat.ofHom (algebraMap (X.presheaf.stalk x)
    (integralClosure (X.presheaf.stalk x) X.functionField)))
  have h := Scheme.Hom.appLE_comp_appLE j (X.fromSpecStalk x) U ⊤ ⊤
    (le_of_eq (fromSpecStalk_preimage X U x).symm) (by simp)
  refine h.symm.trans ?_
  rw [fromSpecStalk_appLE]
  change (X.presheaf.germ U x x.property ≫
    (Scheme.ΓSpecIso (X.presheaf.stalk x)).inv) ≫ j.appTop = _
  rw [Category.assoc, ← Scheme.ΓSpecIso_inv_naturality]

def stalkBaseFieldMap : X.functionField ⟶
    (Spec (.of (integralClosure (X.presheaf.stalk x) X.functionField))).functionField :=
  Cycles.Functoriality.FunctionFields.Construction.genericFieldMap (stalkBaseMap X U x) (stalkBaseMap_genericPoint X U hU x)

theorem stalkBaseFieldMap_section (a : Γ(X, U)) :
    stalkBaseFieldMap X U hU x (X.germToFunctionField U a) =
      StructureSheaf.toStalk (integralClosure (X.presheaf.stalk x) X.functionField)
        (genericPoint (Spec (.of (integralClosure (X.presheaf.stalk x) X.functionField))))
        (algebraMap (X.presheaf.stalk x) (integralClosure (X.presheaf.stalk x) X.functionField)
          (X.presheaf.germ U x x.property a)) := by
  let : Nonempty (⊤ : (Spec (.of
      (integralClosure (X.presheaf.stalk x) X.functionField))).Opens) :=
    ⟨⟨genericPoint _, trivial⟩⟩
  have h := Generic.Fields.genericFieldMap_germ_appLE (stalkBaseMap X U x)
    (stalkBaseMap_genericPoint X U hU x) U ⊤
    (le_of_eq (stalkBaseMap_preimage X U x).symm)
  rw [stalkBaseMap_appLE] at h
  exact congrArg (fun h : Γ(X, U) ⟶
    (Spec (.of (integralClosure (X.presheaf.stalk x) X.functionField))).functionField => h a) h

def stalkNormalizationFieldMap : (Normalization.Scheme.normalization X).functionField ⟶
    (Spec (.of (integralClosure (X.presheaf.stalk x) X.functionField))).functionField :=
  Cycles.Functoriality.FunctionFields.Construction.genericFieldMap (StalkMap.normalizationStalkMap X U hU x)
    (StalkMap.normalizationStalkMap_genericPoint X U hU x)

instance : IsIso (stalkNormalizationFieldMap X U hU x) := by
  let := StalkMap.normalizationStalkMap_stalkMap_isIso X U hU x
    (genericPoint (Spec (.of (integralClosure (X.presheaf.stalk x) X.functionField))))
  unfold stalkNormalizationFieldMap Cycles.Functoriality.FunctionFields.Construction.genericFieldMap
  infer_instance

theorem stalkBaseFieldMap_comp :
    stalkBaseFieldMap X U hU x =
      Fields.normalizationFieldMap X ≫ stalkNormalizationFieldMap X U hU x := by
  exact (Generic.Fields.genericFieldMap_congr
    (StalkMap.normalizationStalkMap_comp X U hU x).symm
    (stalkBaseMap_genericPoint X U hU x)
    ((congrArg (Normalization.Scheme.normalizationMap X) (StalkMap.normalizationStalkMap_genericPoint X U hU x)).trans
      (Fields.normalizationMap_genericPoint X))).trans
        (Generic.Fields.genericFieldMap_comp (StalkMap.normalizationStalkMap X U hU x)
          (Normalization.Scheme.normalizationMap X) (StalkMap.normalizationStalkMap_genericPoint X U hU x)
          (Fields.normalizationMap_genericPoint X))

variable {k : Type u} [Field k] [CharZero k]
  (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] (hx : Order.coheight (x : X) = 1)

theorem normalizedStalkFunction_section (a : Γ(X, U)) :
    NormalizedStalkDivisor.normalizedStalkFunction f x hx (X.germToFunctionField U a) =
      StructureSheaf.toStalk (integralClosure (X.presheaf.stalk x) X.functionField)
        (genericPoint (Spec (.of (integralClosure (X.presheaf.stalk x) X.functionField))))
        (algebraMap (X.presheaf.stalk x) (integralClosure (X.presheaf.stalk x) X.functionField)
          (X.presheaf.germ U x x.property a)) := by
  let R := X.presheaf.stalk x
  let D := integralClosure R X.functionField
  let : IsDedekindDomain D := Support.Normalization.stalk_normalization_isDedekind f x hx
  let : IsFractionRing D X.functionField :=
    integralClosure.isFractionRing_of_finite_extension X.functionField X.functionField
  change Affine.Order.affineFunctionFieldIso D
    ((FractionRing.algEquiv D X.functionField).symm (X.germToFunctionField U a)) = _
  rw [← Scheme.algebraMap_germ_eq_germToFunctionField X x.property a,
    IsScalarTower.algebraMap_apply R D X.functionField, AlgEquiv.commutes, AlgEquiv.commutes]
  rfl

/-- The local function used in the normalization divisor formula is the
pullback of the original rational function through the actual scheme map. -/
theorem stalkBaseFieldMap_eq_normalizedStalkFunction (g : X.functionField) :
    stalkBaseFieldMap X U hU x g =
      NormalizedStalkDivisor.normalizedStalkFunction f x hx g := by
  let R := X.presheaf.stalk x
  let D := integralClosure R X.functionField
  let : IsDedekindDomain D := Support.Normalization.stalk_normalization_isDedekind f x hx
  let : IsFractionRing D X.functionField :=
    integralClosure.isFractionRing_of_finite_extension X.functionField X.functionField
  let := functionField_isFractionRing_of_isAffineOpen X U hU
  have hs (a : Γ(X, U)) :
      stalkBaseFieldMap X U hU x (algebraMap Γ(X, U) X.functionField a) =
        Affine.Order.affineFunctionFieldIso D
          ((FractionRing.algEquiv D X.functionField).symm
            (algebraMap Γ(X, U) X.functionField a)) :=
    (stalkBaseFieldMap_section X U hU x a).trans
      (normalizedStalkFunction_section X U x f hx a).symm
  obtain ⟨a, b, _, rfl⟩ := IsFractionRing.div_surjective Γ(X, U) g
  change stalkBaseFieldMap X U hU x (_ / _) =
    Affine.Order.affineFunctionFieldIso D ((FractionRing.algEquiv D X.functionField).symm (_ / _))
  rw [map_div₀, map_div₀, map_div₀, hs a, hs b]

/-- Pulling the global normalization's rational function to the normalized
stalk gives exactly the local function used in the coefficient formula. -/
theorem normalizationFunction_restrict (g : X.functionField) :
    stalkNormalizationFieldMap X U hU x ((Fields.normalizationFieldIso X).hom g) =
      NormalizedStalkDivisor.normalizedStalkFunction f x hx g := by
  exact (congrArg (fun h : X.functionField ⟶
    (Spec (.of (integralClosure (X.presheaf.stalk x) X.functionField))).functionField => h g)
      (stalkBaseFieldMap_comp X U hU x)).symm.trans
        (stalkBaseFieldMap_eq_normalizedStalkFunction X U hU x f hx g)

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Normalization.StalkFields
