import OAI.AlgebraicGeometry.Divisors.LineBundles.NormalizationResidue

/-! # Normalization Charts -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.NormalizationCharts.BundleCycles

noncomputable section

/-!
# LineBundleCycles: actual integral-closure charts of the normalization

The affine coordinate rings of the constructed normalization identify
with integral closures in the original function field. Their structural
maps are the literal algebra maps from the affine base rings. These are
the charts used to compare the geometric residue cycle with local rings.
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Normalization.Scheme

universe u
variable (X : Scheme.{u}) [IsIntegral X] (U : X.Opens) (hU : IsAffineOpen U) [Nonempty U]

def normalizationAffineRingIso :
    Γ(IntersectionTheory.ProjectionFormula.Normalization.Scheme.normalization X, IntersectionTheory.ProjectionFormula.Normalization.Scheme.normalizationMap X ⁻¹ᵁ U) ≅ CommRingCat.of (integralClosure Γ(X, U) X.functionField) := by
  let := ((IntersectionTheory.ProjectionFormula.Normalization.Scheme.genericMap X).app U).hom.toAlgebra
  exact (IntersectionTheory.ProjectionFormula.Normalization.Scheme.genericMap X).normalizationObjIso hU ≪≫
    (IntersectionTheory.ProjectionFormula.Normalization.Scheme.preimageFieldAlgEquiv X U).mapIntegralClosure.toRingEquiv.toCommRingCatIso

theorem normalizationAffineRingIso_base :
    (IntersectionTheory.ProjectionFormula.Normalization.Scheme.normalizationMap X).app U ≫ (normalizationAffineRingIso X U hU).hom =
      CommRingCat.ofHom (algebraMap Γ(X, U) (integralClosure Γ(X, U) X.functionField)) := by
  let := ((IntersectionTheory.ProjectionFormula.Normalization.Scheme.genericMap X).app U).hom.toAlgebra
  change (IntersectionTheory.ProjectionFormula.Normalization.Scheme.genericMap X).fromNormalization.app U ≫
    ((IntersectionTheory.ProjectionFormula.Normalization.Scheme.genericMap X).normalizationObjIso hU ≪≫
      (IntersectionTheory.ProjectionFormula.Normalization.Scheme.preimageFieldAlgEquiv X U).mapIntegralClosure.toRingEquiv.toCommRingCatIso).hom = _
  rw [(IntersectionTheory.ProjectionFormula.Normalization.Scheme.genericMap X).fromNormalization_app hU, Iso.trans_hom, Category.assoc, Iso.inv_hom_id_assoc]
  ext a
  exact congrArg (fun z : integralClosure Γ(X, U) X.functionField => (z : X.functionField))
    ((IntersectionTheory.ProjectionFormula.Normalization.Scheme.preimageFieldAlgEquiv X U).mapIntegralClosure.commutes a)

def normalizationAffineAlgEquiv :
    letI := ((IntersectionTheory.ProjectionFormula.Normalization.Scheme.normalizationMap X).app U).hom.toAlgebra
    Γ(IntersectionTheory.ProjectionFormula.Normalization.Scheme.normalization X, IntersectionTheory.ProjectionFormula.Normalization.Scheme.normalizationMap X ⁻¹ᵁ U) ≃ₐ[Γ(X, U)] integralClosure Γ(X, U) X.functionField := by
  let := ((IntersectionTheory.ProjectionFormula.Normalization.Scheme.normalizationMap X).app U).hom.toAlgebra
  exact { (normalizationAffineRingIso X U hU).commRingCatIsoToRingEquiv with
    commutes' := fun a => congrArg
      (fun h : Γ(X, U) ⟶ CommRingCat.of (integralClosure Γ(X, U) X.functionField) => h a)
      (normalizationAffineRingIso_base X U hU) }

def normalizationChartMap : Spec (CommRingCat.of (integralClosure Γ(X, U) X.functionField)) ⟶ IntersectionTheory.ProjectionFormula.Normalization.Scheme.normalization X :=
  Spec.map (normalizationAffineRingIso X U hU).hom ≫ (hU.preimage (IntersectionTheory.ProjectionFormula.Normalization.Scheme.normalizationMap X)).fromSpec

instance normalizationChartMap_isOpenImmersion : IsOpenImmersion (normalizationChartMap X U hU) := by
  unfold normalizationChartMap
  infer_instance

theorem normalizationChartMap_comp :
    normalizationChartMap X U hU ≫ IntersectionTheory.ProjectionFormula.Normalization.Scheme.normalizationMap X =
      Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U) (integralClosure Γ(X, U) X.functionField))) ≫ hU.fromSpec := by
  rw [normalizationChartMap, Category.assoc,
    ← hU.SpecMap_appLE_fromSpec (IntersectionTheory.ProjectionFormula.Normalization.Scheme.normalizationMap X) (hU.preimage (IntersectionTheory.ProjectionFormula.Normalization.Scheme.normalizationMap X)) le_rfl,
    ← Category.assoc, ← Spec.map_comp]
  congr 2
  rw [← Scheme.Hom.app_eq_appLE, normalizationAffineRingIso_base]

theorem normalizationChartMap_range :
    Set.range (normalizationChartMap X U hU) = (IntersectionTheory.ProjectionFormula.Normalization.Scheme.normalizationMap X ⁻¹ᵁ U : Set (IntersectionTheory.ProjectionFormula.Normalization.Scheme.normalization X)) := by
  rw [normalizationChartMap, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
    (Spec.map (normalizationAffineRingIso X U hU).hom).surjective.range_eq, Set.image_univ]
  exact (hU.preimage (IntersectionTheory.ProjectionFormula.Normalization.Scheme.normalizationMap X)).range_fromSpec

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.NormalizationCharts.BundleCycles
