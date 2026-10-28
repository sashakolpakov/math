import OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.Field
import OAI.AlgebraicGeometry.CycleClass.Thom.ProperImage.SmoothEtaleOpen
import OAI.AlgebraicGeometry.CycleClass.Thom.ProperImage.RestrictionDegree
import OAI.AlgebraicGeometry.CycleClass.Thom.ProperImage.IntrinsicFiberDegree

/-! # Generic Cover -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.GenericCover.Constructions

noncomputable section

/-! The genuine normalization admits a constructed dense smooth finite étale restriction, whose actual generic residue degree and complex fiber cardinality are one. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.Scheme.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.Fields.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.Field.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X.left] [LocallyOfFiniteType X.hom]

def normalizationOver : Over Foundations.Scheme.ProjectiveSpace.complexBase := Over.mk (Scheme.Constructions.normalizationMap X.left ≫ X.hom)

def normalizationOverMap : normalizationOver X ⟶ X := Over.homMk (Scheme.Constructions.normalizationMap X.left) rfl

instance normalizationOver_integral : IsIntegral (normalizationOver X).left :=
  inferInstanceAs (IsIntegral (Scheme.Constructions.normalization X.left))

instance normalizationOverMap_finite : IsFinite (normalizationOverMap X).left :=
  Scheme.Constructions.normalizationMap_isFinite X.left X.hom

theorem goodOpen_exists :
    ∃ U : X.left.Opens, genericPoint X.left ∈ U ∧
      IsFinite ((normalizationOverMap X).left ∣_ U) ∧ Etale ((normalizationOverMap X).left ∣_ U) ∧
      Smooth (U.ι ≫ X.hom) ∧
      Smooth ((((normalizationOverMap X).left ⁻¹ᵁ U).ι) ≫ (normalizationOver X).hom) := by
  let : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  exact ProperImage.SmoothEtaleOpen.Constructions.Construction.exists_generic_smooth_finiteEtale_open (normalizationOverMap X).left X.hom
    (Fields.Constructions.normalizationMap_genericPoint X.left) (Field.Constructions.finiteNormalization_dimension X.left X.hom).symm

def goodOpen : X.left.Opens := (goodOpen_exists X).choose

theorem goodOpen_spec :
    genericPoint X.left ∈ goodOpen X ∧
      IsFinite ((normalizationOverMap X).left ∣_ goodOpen X) ∧
      Etale ((normalizationOverMap X).left ∣_ goodOpen X) ∧
      Smooth ((goodOpen X).ι ≫ X.hom) ∧
      Smooth ((((normalizationOverMap X).left ⁻¹ᵁ goodOpen X).ι) ≫ (normalizationOver X).hom) :=
  (goodOpen_exists X).choose_spec

instance goodOpen_nonempty : Nonempty (goodOpen X) := ⟨⟨genericPoint X.left, (goodOpen_spec X).1⟩⟩

instance sourceOpen_nonempty : Nonempty ((normalizationOverMap X).left ⁻¹ᵁ goodOpen X) :=
  ⟨⟨genericPoint (normalizationOver X).left, by
    change Scheme.Constructions.normalizationMap X.left (genericPoint (Scheme.Constructions.normalization X.left)) ∈ goodOpen X
    rw [Fields.Constructions.normalizationMap_genericPoint]
    exact (goodOpen_spec X).1⟩⟩

def sourceOpen : Over Foundations.Scheme.ProjectiveSpace.complexBase :=
  ProperImage.AnalyticRestriction.Constructions.Construction.openSchemeOver (normalizationOver X) ((normalizationOverMap X).left ⁻¹ᵁ goodOpen X)

def targetOpen : Over Foundations.Scheme.ProjectiveSpace.complexBase := ProperImage.AnalyticRestriction.Constructions.Construction.openSchemeOver X (goodOpen X)

instance sourceOpen_integral : IsIntegral (sourceOpen X).left :=
  inferInstanceAs (IsIntegral (ProperImage.AnalyticRestriction.Constructions.Construction.openSchemeOver (normalizationOver X)
    ((normalizationOverMap X).left ⁻¹ᵁ goodOpen X)).left)

instance targetOpen_integral : IsIntegral (targetOpen X).left :=
  inferInstanceAs (IsIntegral (ProperImage.AnalyticRestriction.Constructions.Construction.openSchemeOver X (goodOpen X)).left)

instance sourceOpen_smooth : Smooth (sourceOpen X).hom := (goodOpen_spec X).2.2.2.2
instance targetOpen_smooth : Smooth (targetOpen X).hom := (goodOpen_spec X).2.2.2.1

def coverMap : sourceOpen X ⟶ targetOpen X := ProperImage.AnalyticRestriction.Constructions.Construction.restrictedSchemeMap (normalizationOverMap X) (goodOpen X)

instance coverMap_finite : IsFinite (coverMap X).left := (goodOpen_spec X).2.1
instance coverMap_etale : Etale (coverMap X).left := (goodOpen_spec X).2.2.1

theorem coverMap_genericPoint :
    (coverMap X).left (genericPoint (sourceOpen X).left) = genericPoint (targetOpen X).left :=
  ProperImage.RestrictionDegree.Constructions.Construction.restrictedSchemeMap_genericPoint (normalizationOverMap X) (Fields.Constructions.normalizationMap_genericPoint X.left) (goodOpen X)

theorem coverMap_residueDegree : (coverMap X).left.residueDegree (genericPoint (sourceOpen X).left) = 1 :=
  (ProperImage.RestrictionDegree.Constructions.Construction.restrictedSchemeMap_residueDegree (normalizationOverMap X) (goodOpen X)).trans
    (Scheme.Constructions.normalizationMap_generic_residueDegree X.left)

theorem coverMap_complexFiber_card (x : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (targetOpen X)) :
    Nat.card {y : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (sourceOpen X) | ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (coverMap X) y = x} = 1 :=
  (ProperImage.IntrinsicFiberDegree.Constructions.Construction.native_fiber_card_eq_residueDegree (coverMap X) (coverMap_genericPoint X) x).trans
    (coverMap_residueDegree X)

theorem goodOpen_subset_smoothLocus : goodOpen X ≤ X.hom.smoothLocus := by
  let : Smooth ((goodOpen X).ι ≫ X.hom) := (goodOpen_spec X).2.2.2.1
  exact ProperImage.RestrictionDegree.Constructions.Construction.open_subset_smoothLocus X.hom _

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.GenericCover.Constructions
