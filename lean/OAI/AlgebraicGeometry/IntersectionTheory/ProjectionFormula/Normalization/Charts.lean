import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Normalization.Fields
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Divisor.DivisorRestriction

/-! # Charts -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Normalization.Charts

noncomputable section

/-! Affine charts of the constructed global normalization are the actual
integral closures in the original function field, compatibly with the
normalization morphism. -/

set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Normalization.Scheme

universe u

variable (X : Scheme.{u}) [IsIntegral X]
  (U : X.Opens) (hU : IsAffineOpen U) [Nonempty U]

/-- The actual coordinate ring of a normalization chart, expressed in the
original scheme's function field. -/
def normalizationAffineRingIso :
    Γ(Normalization.Scheme.normalization X, Normalization.Scheme.normalizationMap X ⁻¹ᵁ U) ≅
      .of (integralClosure Γ(X, U) X.functionField) := by
  let := ((Normalization.Scheme.genericMap X).app U).hom.toAlgebra
  exact (Normalization.Scheme.genericMap X).normalizationObjIso hU ≪≫
    (Normalization.Scheme.preimageFieldAlgEquiv X U).mapIntegralClosure.toRingEquiv.toCommRingCatIso

theorem normalizationAffineRingIso_base :
    (Normalization.Scheme.normalizationMap X).app U ≫ (normalizationAffineRingIso X U hU).hom =
      CommRingCat.ofHom (algebraMap Γ(X, U) (integralClosure Γ(X, U) X.functionField)) := by
  let := ((Normalization.Scheme.genericMap X).app U).hom.toAlgebra
  change (Normalization.Scheme.genericMap X).fromNormalization.app U ≫
    ((Normalization.Scheme.genericMap X).normalizationObjIso hU ≪≫
      (Normalization.Scheme.preimageFieldAlgEquiv X U).mapIntegralClosure.toRingEquiv.toCommRingCatIso).hom = _
  rw [(Normalization.Scheme.genericMap X).fromNormalization_app hU, Iso.trans_hom, Category.assoc,
    Iso.inv_hom_id_assoc]
  ext a
  exact congrArg (fun z : integralClosure Γ(X, U) X.functionField => (z : X.functionField))
    ((Normalization.Scheme.preimageFieldAlgEquiv X U).mapIntegralClosure.commutes a)

def normalizationAffineAlgEquiv :
    letI := ((Normalization.Scheme.normalizationMap X).app U).hom.toAlgebra
    Γ(Normalization.Scheme.normalization X, Normalization.Scheme.normalizationMap X ⁻¹ᵁ U) ≃ₐ[Γ(X, U)]
      integralClosure Γ(X, U) X.functionField := by
  let := ((Normalization.Scheme.normalizationMap X).app U).hom.toAlgebra
  exact { (normalizationAffineRingIso X U hU).commRingCatIsoToRingEquiv with
    commutes' := fun a => congrArg
      (fun h : Γ(X, U) ⟶ CommRingCat.of (integralClosure Γ(X, U) X.functionField) => h a)
      (normalizationAffineRingIso_base X U hU) }

/-- The normalization chart is the spectrum of the integral closure. -/
def normalizationChartMap :
    Spec (.of (integralClosure Γ(X, U) X.functionField)) ⟶ Normalization.Scheme.normalization X :=
  Spec.map (normalizationAffineRingIso X U hU).hom ≫
    (hU.preimage (Normalization.Scheme.normalizationMap X)).fromSpec

instance : IsOpenImmersion (normalizationChartMap X U hU) := by
  unfold normalizationChartMap
  infer_instance

theorem normalizationChartMap_comp :
    normalizationChartMap X U hU ≫ Normalization.Scheme.normalizationMap X =
      Spec.map (CommRingCat.ofHom
        (algebraMap Γ(X, U) (integralClosure Γ(X, U) X.functionField))) ≫ hU.fromSpec := by
  rw [normalizationChartMap, Category.assoc,
    ← hU.SpecMap_appLE_fromSpec (Normalization.Scheme.normalizationMap X)
      (hU.preimage (Normalization.Scheme.normalizationMap X)) le_rfl,
    ← Category.assoc, ← Spec.map_comp]
  congr 2
  rw [← Scheme.Hom.app_eq_appLE, normalizationAffineRingIso_base]

theorem normalizationChartMap_range :
    Set.range (normalizationChartMap X U hU) =
      (Normalization.Scheme.normalizationMap X ⁻¹ᵁ U : Set (Normalization.Scheme.normalization X)) := by
  rw [normalizationChartMap, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
    (Spec.map (normalizationAffineRingIso X U hU).hom).surjective.range_eq, Set.image_univ]
  exact (hU.preimage (Normalization.Scheme.normalizationMap X)).range_fromSpec

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Normalization.Charts
