import OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.Field

/-! # Charts -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.Charts.Constructions

noncomputable section

/-!
# ThomClass: actual integral-closure charts of the normalization

The affine coordinate rings of the constructed normalization identify
with integral closures in the original function field. Their structural
maps are the literal algebra maps from the affine base rings. These are
the charts used to compare the geometric residue cycle with local rings.
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory

open OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.Scheme.Constructions

universe u
variable (X : Scheme.{u}) [IsIntegral X] (U : X.Opens) (hU : IsAffineOpen U) [Nonempty U]

def normalizationAffineRingIso :
    Γ(Normalization.Scheme.Constructions.normalization X, Normalization.Scheme.Constructions.normalizationMap X ⁻¹ᵁ U) ≅ CommRingCat.of (integralClosure Γ(X, U) X.functionField) := by
  let := ((Normalization.Scheme.Constructions.genericMap X).app U).hom.toAlgebra
  exact (Normalization.Scheme.Constructions.genericMap X).normalizationObjIso hU ≪≫
    (Normalization.Scheme.Constructions.preimageFieldAlgEquiv X U).mapIntegralClosure.toRingEquiv.toCommRingCatIso

theorem normalizationAffineRingIso_base :
    (Normalization.Scheme.Constructions.normalizationMap X).app U ≫ (normalizationAffineRingIso X U hU).hom =
      CommRingCat.ofHom (algebraMap Γ(X, U) (integralClosure Γ(X, U) X.functionField)) := by
  let := ((Normalization.Scheme.Constructions.genericMap X).app U).hom.toAlgebra
  change (Normalization.Scheme.Constructions.genericMap X).fromNormalization.app U ≫
    ((Normalization.Scheme.Constructions.genericMap X).normalizationObjIso hU ≪≫
      (Normalization.Scheme.Constructions.preimageFieldAlgEquiv X U).mapIntegralClosure.toRingEquiv.toCommRingCatIso).hom = _
  rw [(Normalization.Scheme.Constructions.genericMap X).fromNormalization_app hU, Iso.trans_hom, Category.assoc, Iso.inv_hom_id_assoc]
  ext a
  exact congrArg (fun z : integralClosure Γ(X, U) X.functionField => (z : X.functionField))
    ((Normalization.Scheme.Constructions.preimageFieldAlgEquiv X U).mapIntegralClosure.commutes a)

def normalizationAffineAlgEquiv :
    letI := ((Normalization.Scheme.Constructions.normalizationMap X).app U).hom.toAlgebra
    Γ(Normalization.Scheme.Constructions.normalization X, Normalization.Scheme.Constructions.normalizationMap X ⁻¹ᵁ U) ≃ₐ[Γ(X, U)] integralClosure Γ(X, U) X.functionField := by
  let := ((Normalization.Scheme.Constructions.normalizationMap X).app U).hom.toAlgebra
  exact { (normalizationAffineRingIso X U hU).commRingCatIsoToRingEquiv with
    commutes' := fun a => congrArg
      (fun h : Γ(X, U) ⟶ CommRingCat.of (integralClosure Γ(X, U) X.functionField) => h a)
      (normalizationAffineRingIso_base X U hU) }

def normalizationChartMap : Spec (CommRingCat.of (integralClosure Γ(X, U) X.functionField)) ⟶ Normalization.Scheme.Constructions.normalization X :=
  Spec.map (normalizationAffineRingIso X U hU).hom ≫ (hU.preimage (Normalization.Scheme.Constructions.normalizationMap X)).fromSpec

instance normalizationChartMap_isOpenImmersion : IsOpenImmersion (normalizationChartMap X U hU) := by
  unfold normalizationChartMap
  infer_instance

theorem normalizationChartMap_comp :
    normalizationChartMap X U hU ≫ Normalization.Scheme.Constructions.normalizationMap X =
      Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U) (integralClosure Γ(X, U) X.functionField))) ≫ hU.fromSpec := by
  rw [normalizationChartMap, Category.assoc,
    ← hU.SpecMap_appLE_fromSpec (Normalization.Scheme.Constructions.normalizationMap X) (hU.preimage (Normalization.Scheme.Constructions.normalizationMap X)) le_rfl,
    ← Category.assoc, ← Spec.map_comp]
  congr 2
  rw [← Scheme.Hom.app_eq_appLE, normalizationAffineRingIso_base]

theorem normalizationChartMap_range :
    Set.range (normalizationChartMap X U hU) = (Normalization.Scheme.Constructions.normalizationMap X ⁻¹ᵁ U : Set (Normalization.Scheme.Constructions.normalization X)) := by
  rw [normalizationChartMap, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
    (Spec.map (normalizationAffineRingIso X U hU).hom).surjective.range_eq, Set.image_univ]
  exact (hU.preimage (Normalization.Scheme.Constructions.normalizationMap X)).range_fromSpec

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.Charts.Constructions
