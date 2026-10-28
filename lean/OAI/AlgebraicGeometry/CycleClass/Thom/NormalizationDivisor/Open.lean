import OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationDivisor.Image
import OAI.AlgebraicGeometry.CycleClass.Thom.Finite.SupportGoodOpen

/-! # Open -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationDivisor.Open

noncomputable section

section

/-! The actual map from a normalized prime support to its ambient reduced
image, retaining the original generic point and residue-field multiplicity. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Constructions.Map

open OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.AmbientMap.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.AmbientTopology.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.PrincipalBoundary.Constructions
  Image.Constructions SchemeDivisor.Purity.Constructions Scheme.RegularSupport.Constructions

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (W : IrreducibleCloseds V.carrier)

local instance : AlgebraicGeometry.IsNoetherian V.carrier := Foundations.Scheme.ClosedProjective.isNoetherian_of_isProper_toSpec V.structureMap
local instance : Smooth (Normalization.AmbientMap.Constructions.smoothNormalizationOver V W).hom := Normalization.AmbientMap.Constructions.smoothNormalization_smooth V W
local instance : IsFinite (Normalization.AmbientMap.Constructions.smoothNormalizationToAmbient V W).left := Normalization.AmbientMap.Constructions.smoothNormalization_finite V W
local instance : QuasiCompact (ProperImage.AnalyticRestriction.Constructions.Construction.openSchemeInclusion V.toOver (Normalization.AmbientMap.Constructions.ambientOpen V W)).left :=
  inferInstanceAs (QuasiCompact (Normalization.AmbientMap.Constructions.ambientOpen V W).ι)

variable (z : {x : (Normalization.AmbientMap.Constructions.smoothNormalizationOver V W).left // Order.coheight x = 1})

abbrev sourceSupport := Scheme.RegularSupport.Constructions.supportOver (Normalization.AmbientMap.Constructions.smoothNormalizationOver V W) (SchemeDivisor.Purity.Constructions.primeSupport (Normalization.AmbientMap.Constructions.smoothNormalizationOver V W) z)

abbrev openImageSupport := Scheme.RegularSupport.Constructions.supportOver (ProperImage.AnalyticRestriction.Constructions.Construction.openSchemeOver V.toOver (Normalization.AmbientMap.Constructions.ambientOpen V W))
  (Scheme.ProperSupport.Constructions.imageSupport (Normalization.AmbientMap.Constructions.smoothNormalizationToAmbient V W)
    (SchemeDivisor.Purity.Constructions.primeSupport (Normalization.AmbientMap.Constructions.smoothNormalizationOver V W) z))

abbrev targetSupport := Scheme.RegularSupport.Constructions.supportOver V.toOver (Image.Constructions.imageSupport V W z)

def finiteSupportMap : sourceSupport V W z ⟶ openImageSupport V W z :=
  Scheme.ProperSupport.Constructions.imageOverMap (Normalization.AmbientMap.Constructions.smoothNormalizationToAmbient V W)
    (SchemeDivisor.Purity.Constructions.primeSupport (Normalization.AmbientMap.Constructions.smoothNormalizationOver V W) z)

instance finiteSupportMap_finite : IsFinite (finiteSupportMap V W z).left :=
  Scheme.ProperSupport.Constructions.imageMap_finite (Normalization.AmbientMap.Constructions.smoothNormalizationToAmbient V W)
    (SchemeDivisor.Purity.Constructions.primeSupport (Normalization.AmbientMap.Constructions.smoothNormalizationOver V W) z)

def imageClosureMap : openImageSupport V W z ⟶ targetSupport V W z :=
  Scheme.OpenSupportClosure.Constructions.toClosureOver (ProperImage.AnalyticRestriction.Constructions.Construction.openSchemeInclusion V.toOver (Normalization.AmbientMap.Constructions.ambientOpen V W))
    (Scheme.ProperSupport.Constructions.imageSupport (Normalization.AmbientMap.Constructions.smoothNormalizationToAmbient V W)
      (SchemeDivisor.Purity.Constructions.primeSupport (Normalization.AmbientMap.Constructions.smoothNormalizationOver V W) z))

instance imageClosureMap_open : IsOpenImmersion (imageClosureMap V W z).left :=
  inferInstanceAs (IsOpenImmersion (Scheme.OpenSupportClosure.Constructions.toClosure
    (ProperImage.AnalyticRestriction.Constructions.Construction.openSchemeInclusion V.toOver (Normalization.AmbientMap.Constructions.ambientOpen V W))
    (Scheme.ProperSupport.Constructions.imageSupport (Normalization.AmbientMap.Constructions.smoothNormalizationToAmbient V W)
      (SchemeDivisor.Purity.Constructions.primeSupport (Normalization.AmbientMap.Constructions.smoothNormalizationOver V W) z))))

/-- The map is the actual finite support map followed by the actual open
immersion into the reduced projective closure. -/
def divisorMap : sourceSupport V W z ⟶ targetSupport V W z :=
  finiteSupportMap V W z ≫ imageClosureMap V W z

theorem imageClosureMap_ambient :
    imageClosureMap V W z ≫ Scheme.RegularSupport.Constructions.supportToAmbient V.toOver (Image.Constructions.imageSupport V W z) =
    Scheme.RegularSupport.Constructions.supportToAmbient (ProperImage.AnalyticRestriction.Constructions.Construction.openSchemeOver V.toOver (Normalization.AmbientMap.Constructions.ambientOpen V W))
      (Scheme.ProperSupport.Constructions.imageSupport (Normalization.AmbientMap.Constructions.smoothNormalizationToAmbient V W)
        (SchemeDivisor.Purity.Constructions.primeSupport (Normalization.AmbientMap.Constructions.smoothNormalizationOver V W) z)) ≫ ProperImage.AnalyticRestriction.Constructions.Construction.openSchemeInclusion V.toOver (Normalization.AmbientMap.Constructions.ambientOpen V W) :=
  Scheme.OpenSupportClosure.Constructions.toClosureOver_ambient
    (ProperImage.AnalyticRestriction.Constructions.Construction.openSchemeInclusion V.toOver (Normalization.AmbientMap.Constructions.ambientOpen V W))
    (Scheme.ProperSupport.Constructions.imageSupport (Normalization.AmbientMap.Constructions.smoothNormalizationToAmbient V W)
      (SchemeDivisor.Purity.Constructions.primeSupport (Normalization.AmbientMap.Constructions.smoothNormalizationOver V W) z))

theorem finiteSupportMap_ambient :
    finiteSupportMap V W z ≫ Scheme.RegularSupport.Constructions.supportToAmbient (ProperImage.AnalyticRestriction.Constructions.Construction.openSchemeOver V.toOver (Normalization.AmbientMap.Constructions.ambientOpen V W))
      (Scheme.ProperSupport.Constructions.imageSupport (Normalization.AmbientMap.Constructions.smoothNormalizationToAmbient V W)
        (SchemeDivisor.Purity.Constructions.primeSupport (Normalization.AmbientMap.Constructions.smoothNormalizationOver V W) z)) =
    Scheme.RegularSupport.Constructions.supportToAmbient (Normalization.AmbientMap.Constructions.smoothNormalizationOver V W) (SchemeDivisor.Purity.Constructions.primeSupport (Normalization.AmbientMap.Constructions.smoothNormalizationOver V W) z) ≫
      Normalization.AmbientMap.Constructions.smoothNormalizationToAmbient V W :=
  Scheme.ProperSupport.Constructions.imageOverMap_inclusion (Normalization.AmbientMap.Constructions.smoothNormalizationToAmbient V W)
    (SchemeDivisor.Purity.Constructions.primeSupport (Normalization.AmbientMap.Constructions.smoothNormalizationOver V W) z)

theorem divisorMap_ambient :
    divisorMap V W z ≫ Scheme.RegularSupport.Constructions.supportToAmbient V.toOver (Image.Constructions.imageSupport V W z) =
      Scheme.RegularSupport.Constructions.supportToAmbient (Normalization.AmbientMap.Constructions.smoothNormalizationOver V W) (SchemeDivisor.Purity.Constructions.primeSupport (Normalization.AmbientMap.Constructions.smoothNormalizationOver V W) z) ≫
        Normalization.PrincipalBoundary.Constructions.fullAmbientMap V W := by
  rw [divisorMap, Category.assoc, imageClosureMap_ambient,
    ← Category.assoc, finiteSupportMap_ambient, Category.assoc]
  rfl

local instance : IsIntegral (sourceSupport V W z).left :=
  inferInstanceAs (IsIntegral (Geometric.GenericPoint.reducedSupportScheme (SchemeDivisor.Purity.Constructions.primeSupport (Normalization.AmbientMap.Constructions.smoothNormalizationOver V W) z)))
local instance : IsIntegral (openImageSupport V W z).left :=
  inferInstanceAs (IsIntegral (Geometric.GenericPoint.reducedSupportScheme (Scheme.ProperSupport.Constructions.imageSupport
    (Normalization.AmbientMap.Constructions.smoothNormalizationToAmbient V W) (SchemeDivisor.Purity.Constructions.primeSupport (Normalization.AmbientMap.Constructions.smoothNormalizationOver V W) z))))
local instance : IsIntegral (targetSupport V W z).left :=
  inferInstanceAs (IsIntegral (Geometric.GenericPoint.reducedSupportScheme (Image.Constructions.imageSupport V W z)))

theorem finiteSupportMap_genericPoint :
    (finiteSupportMap V W z).left (genericPoint (sourceSupport V W z).left) =
      genericPoint (openImageSupport V W z).left :=
  Scheme.ProperSupport.Constructions.imageMap_genericPoint (Normalization.AmbientMap.Constructions.smoothNormalizationToAmbient V W)
    (SchemeDivisor.Purity.Constructions.primeSupport (Normalization.AmbientMap.Constructions.smoothNormalizationOver V W) z)

theorem divisorMap_genericPoint :
    (divisorMap V W z).left (genericPoint (sourceSupport V W z).left) =
      genericPoint (targetSupport V W z).left := by
  change (imageClosureMap V W z).left
    ((finiteSupportMap V W z).left (genericPoint (sourceSupport V W z).left)) = _
  rw [finiteSupportMap_genericPoint, genericPoint_eq_of_isOpenImmersion]

theorem finiteSupportMap_residueDegree :
    (finiteSupportMap V W z).left.residueDegree (genericPoint (sourceSupport V W z).left) =
      (Normalization.PrincipalBoundary.Constructions.fullAmbientMap V W).left.residueDegree z.val := by
  have h := Scheme.ProperSupport.Constructions.imageMap_residueDegree (Normalization.AmbientMap.Constructions.smoothNormalizationToAmbient V W)
    (SchemeDivisor.Purity.Constructions.primeSupport (Normalization.AmbientMap.Constructions.smoothNormalizationOver V W) z)
  simp only [SchemeDivisor.Purity.Constructions.primeSupport, OrderIso.apply_symm_apply] at h
  exact h.trans (Image.Constructions.image_residueDegree V W z)

theorem divisorMap_residueDegree :
    (divisorMap V W z).left.residueDegree (genericPoint (sourceSupport V W z).left) =
      (Normalization.PrincipalBoundary.Constructions.fullAmbientMap V W).left.residueDegree z.val :=
  (ProperImage.ResidueDegree.Constructions.Construction.residueDegree_post_immersion (finiteSupportMap V W z).left
    (imageClosureMap V W z).left (genericPoint (sourceSupport V W z).left)).trans
    (finiteSupportMap_residueDegree V W z)

end Constructions.Map

end

section

/-! Constructed smooth finite-etale generic opens for each actual prime
divisor of the smooth normalization, with its exact residue degree. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Constructions.Etale

open OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.AmbientMap.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.AmbientTopology.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.PrincipalBoundary.Constructions
  Map SchemeDivisor.Purity.Constructions Scheme.RegularSupport.Constructions

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (W : IrreducibleCloseds V.carrier)

local instance : Smooth (Normalization.AmbientMap.Constructions.smoothNormalizationOver V W).hom := Normalization.AmbientMap.Constructions.smoothNormalization_smooth V W
local instance : IsFinite (Normalization.AmbientMap.Constructions.smoothNormalizationToAmbient V W).left := Normalization.AmbientMap.Constructions.smoothNormalization_finite V W
local instance : LocallyOfFiniteType (ProperImage.AnalyticRestriction.Constructions.Construction.openSchemeOver V.toOver (Normalization.AmbientMap.Constructions.ambientOpen V W)).hom :=
  inferInstanceAs (LocallyOfFiniteType ((Normalization.AmbientMap.Constructions.ambientOpen V W).ι ≫ V.structureMap))

variable (z : {x : (Normalization.AmbientMap.Constructions.smoothNormalizationOver V W).left // Order.coheight x = 1})

instance sourceSupport_integral : IsIntegral (Map.sourceSupport V W z).left :=
  inferInstanceAs (IsIntegral (Geometric.GenericPoint.reducedSupportScheme (SchemeDivisor.Purity.Constructions.primeSupport (Normalization.AmbientMap.Constructions.smoothNormalizationOver V W) z)))

instance openImageSupport_integral : IsIntegral (Map.openImageSupport V W z).left :=
  inferInstanceAs (IsIntegral (Geometric.GenericPoint.reducedSupportScheme (Scheme.ProperSupport.Constructions.imageSupport
    (Normalization.AmbientMap.Constructions.smoothNormalizationToAmbient V W) (SchemeDivisor.Purity.Constructions.primeSupport (Normalization.AmbientMap.Constructions.smoothNormalizationOver V W) z))))

instance targetSupport_integral : IsIntegral (Map.targetSupport V W z).left :=
  inferInstanceAs (IsIntegral (Geometric.GenericPoint.reducedSupportScheme (Image.Constructions.imageSupport V W z)))

theorem goodOpen_exists :
    ∃ U : (Map.openImageSupport V W z).left.Opens,
      genericPoint (Map.openImageSupport V W z).left ∈ U ∧
      IsFinite ((Map.finiteSupportMap V W z).left ∣_ U) ∧
      Etale ((Map.finiteSupportMap V W z).left ∣_ U) ∧
      Smooth (U.ι ≫ (Map.openImageSupport V W z).hom) ∧
      Smooth (((Map.finiteSupportMap V W z).left ⁻¹ᵁ U).ι ≫ (Map.sourceSupport V W z).hom) :=
  Finite.SupportGoodOpen.Constructions.exists_smooth_etale_open (Normalization.AmbientMap.Constructions.smoothNormalizationToAmbient V W)
    (SchemeDivisor.Purity.Constructions.primeSupport (Normalization.AmbientMap.Constructions.smoothNormalizationOver V W) z)

def goodOpen : (Map.openImageSupport V W z).left.Opens := (goodOpen_exists V W z).choose

theorem goodOpen_spec :
    genericPoint (Map.openImageSupport V W z).left ∈ goodOpen V W z ∧
      IsFinite ((Map.finiteSupportMap V W z).left ∣_ goodOpen V W z) ∧
      Etale ((Map.finiteSupportMap V W z).left ∣_ goodOpen V W z) ∧
      Smooth ((goodOpen V W z).ι ≫ (Map.openImageSupport V W z).hom) ∧
      Smooth (((Map.finiteSupportMap V W z).left ⁻¹ᵁ goodOpen V W z).ι ≫ (Map.sourceSupport V W z).hom) :=
  (goodOpen_exists V W z).choose_spec

instance goodOpen_nonempty : Nonempty (goodOpen V W z) :=
  ⟨⟨genericPoint (Map.openImageSupport V W z).left, (goodOpen_spec V W z).1⟩⟩

instance goodOpen_preimage_nonempty : Nonempty ((Map.finiteSupportMap V W z).left ⁻¹ᵁ goodOpen V W z) :=
  ⟨⟨genericPoint (Map.sourceSupport V W z).left, by
    change (Map.finiteSupportMap V W z).left (genericPoint (Map.sourceSupport V W z).left) ∈ goodOpen V W z
    rw [Map.finiteSupportMap_genericPoint]
    exact (goodOpen_spec V W z).1⟩⟩

def sourceOpen : Over Foundations.Scheme.ProjectiveSpace.complexBase :=
  ProperImage.AnalyticRestriction.Constructions.Construction.openSchemeOver (Map.sourceSupport V W z) ((Map.finiteSupportMap V W z).left ⁻¹ᵁ goodOpen V W z)

def targetOpen : Over Foundations.Scheme.ProjectiveSpace.complexBase := ProperImage.AnalyticRestriction.Constructions.Construction.openSchemeOver (Map.openImageSupport V W z) (goodOpen V W z)

instance sourceOpen_integral : IsIntegral (sourceOpen V W z).left :=
  inferInstanceAs (IsIntegral (ProperImage.AnalyticRestriction.Constructions.Construction.openSchemeOver (Map.sourceSupport V W z)
    ((Map.finiteSupportMap V W z).left ⁻¹ᵁ goodOpen V W z)).left)

instance targetOpen_integral : IsIntegral (targetOpen V W z).left :=
  inferInstanceAs (IsIntegral (ProperImage.AnalyticRestriction.Constructions.Construction.openSchemeOver (Map.openImageSupport V W z) (goodOpen V W z)).left)

instance sourceOpen_smooth : Smooth (sourceOpen V W z).hom := (goodOpen_spec V W z).2.2.2.2
instance targetOpen_smooth : Smooth (targetOpen V W z).hom := (goodOpen_spec V W z).2.2.2.1

def coverMap : sourceOpen V W z ⟶ targetOpen V W z :=
  ProperImage.AnalyticRestriction.Constructions.Construction.restrictedSchemeMap (Map.finiteSupportMap V W z) (goodOpen V W z)

instance coverMap_finite : IsFinite (coverMap V W z).left := (goodOpen_spec V W z).2.1
instance coverMap_etale : Etale (coverMap V W z).left := (goodOpen_spec V W z).2.2.1

theorem coverMap_genericPoint :
    (coverMap V W z).left (genericPoint (sourceOpen V W z).left) =
      genericPoint (targetOpen V W z).left :=
  ProperImage.RestrictionDegree.Constructions.Construction.restrictedSchemeMap_genericPoint (Map.finiteSupportMap V W z) (Map.finiteSupportMap_genericPoint V W z) (goodOpen V W z)

theorem coverMap_residueDegree :
    (coverMap V W z).left.residueDegree (genericPoint (sourceOpen V W z).left) =
      (Normalization.PrincipalBoundary.Constructions.fullAmbientMap V W).left.residueDegree z.val :=
  (ProperImage.RestrictionDegree.Constructions.Construction.restrictedSchemeMap_residueDegree (Map.finiteSupportMap V W z) (goodOpen V W z)).trans
    (Map.finiteSupportMap_residueDegree V W z)

theorem coverMap_analytic_proper : IsProperMap (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (coverMap V W z)) :=
  Integral.SchemeProper.Constructions.isProperMap_integral (coverMap V W z)

end Constructions.Etale

end

/-! The constructed normalization cover maps by genuine open immersions
into the original source and target regular loci. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Constructions.Regular

open OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.AmbientMap.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.AmbientTopology.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.PrincipalBoundary.Constructions
  Map Constructions.Etale SchemeDivisor.Purity.Constructions Scheme.RegularSupport.Constructions

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (W : IrreducibleCloseds V.carrier)

local instance : Smooth (Normalization.AmbientMap.Constructions.smoothNormalizationOver V W).hom := Normalization.AmbientMap.Constructions.smoothNormalization_smooth V W
local instance : LocallyOfFiniteType V.toOver.hom := inferInstanceAs (LocallyOfFiniteType V.structureMap)

variable (z : {x : (Normalization.AmbientMap.Constructions.smoothNormalizationOver V W).left // Order.coheight x = 1})

local instance : LocallyOfFinitePresentation (Map.sourceSupport V W z).hom :=
  inferInstanceAs (LocallyOfFinitePresentation
    (Geometric.SupportFiniteType.supportStructureMap (SchemeDivisor.Purity.Constructions.primeSupport (Normalization.AmbientMap.Constructions.smoothNormalizationOver V W) z) (Normalization.AmbientMap.Constructions.smoothNormalizationOver V W).hom))

theorem sourceOpen_subset_smoothLocus :
    (Map.finiteSupportMap V W z).left ⁻¹ᵁ Constructions.Etale.goodOpen V W z ≤ (Map.sourceSupport V W z).hom.smoothLocus := by
  let : Smooth (((Map.finiteSupportMap V W z).left ⁻¹ᵁ Constructions.Etale.goodOpen V W z).ι ≫ (Map.sourceSupport V W z).hom) :=
    (Constructions.Etale.goodOpen_spec V W z).2.2.2.2
  exact ProperImage.RestrictionDegree.Constructions.Construction.open_subset_smoothLocus (Map.sourceSupport V W z).hom _

def sourceToRegular : Constructions.Etale.sourceOpen V W z ⟶
    Scheme.RegularSupport.Constructions.regularOver (Normalization.AmbientMap.Constructions.smoothNormalizationOver V W) (SchemeDivisor.Purity.Constructions.primeSupport (Normalization.AmbientMap.Constructions.smoothNormalizationOver V W) z) :=
  Scheme.SmoothSupportOpen.Constructions.smoothOpenToRegular (Normalization.AmbientMap.Constructions.smoothNormalizationOver V W)
    (SchemeDivisor.Purity.Constructions.primeSupport (Normalization.AmbientMap.Constructions.smoothNormalizationOver V W) z) _ (sourceOpen_subset_smoothLocus V W z)

instance sourceToRegular_open : IsOpenImmersion (sourceToRegular V W z).left :=
  inferInstanceAs (IsOpenImmersion (Scheme.SmoothSupportOpen.Constructions.smoothOpenToRegular (Normalization.AmbientMap.Constructions.smoothNormalizationOver V W)
    (SchemeDivisor.Purity.Constructions.primeSupport (Normalization.AmbientMap.Constructions.smoothNormalizationOver V W) z) _ (sourceOpen_subset_smoothLocus V W z)).left)

def targetToSupport : Constructions.Etale.targetOpen V W z ⟶ Map.targetSupport V W z :=
  ProperImage.AnalyticRestriction.Constructions.Construction.openSchemeInclusion (Map.openImageSupport V W z) (Constructions.Etale.goodOpen V W z) ≫ Map.imageClosureMap V W z

instance targetToSupport_open : IsOpenImmersion (targetToSupport V W z).left := by
  change IsOpenImmersion ((Constructions.Etale.goodOpen V W z).ι ≫ (Map.imageClosureMap V W z).left)
  infer_instance

def targetToRegular : Constructions.Etale.targetOpen V W z ⟶
    Scheme.RegularSupport.Constructions.regularOver V.toOver (Image.Constructions.imageSupport V W z) :=
  Scheme.OpenSupportClosure.Constructions.smoothOpenToRegular (Y := V.toOver)
    (Image.Constructions.imageSupport V W z) (targetToSupport V W z)

instance targetToRegular_open : IsOpenImmersion (targetToRegular V W z).left :=
  inferInstanceAs (IsOpenImmersion (Scheme.OpenSupportClosure.Constructions.smoothOpenToRegular (Y := V.toOver)
    (Image.Constructions.imageSupport V W z) (targetToSupport V W z)).left)

theorem sourceToRegular_ambient :
    sourceToRegular V W z ≫ Scheme.RegularSupport.Constructions.regularToAmbient (Normalization.AmbientMap.Constructions.smoothNormalizationOver V W)
      (SchemeDivisor.Purity.Constructions.primeSupport (Normalization.AmbientMap.Constructions.smoothNormalizationOver V W) z) =
    ProperImage.AnalyticRestriction.Constructions.Construction.openSchemeInclusion (Map.sourceSupport V W z) ((Map.finiteSupportMap V W z).left ⁻¹ᵁ Constructions.Etale.goodOpen V W z) ≫
      Scheme.RegularSupport.Constructions.supportToAmbient (Normalization.AmbientMap.Constructions.smoothNormalizationOver V W) (SchemeDivisor.Purity.Constructions.primeSupport (Normalization.AmbientMap.Constructions.smoothNormalizationOver V W) z) :=
  Scheme.SmoothSupportOpen.Constructions.smoothOpenToRegular_ambient (Normalization.AmbientMap.Constructions.smoothNormalizationOver V W)
    (SchemeDivisor.Purity.Constructions.primeSupport (Normalization.AmbientMap.Constructions.smoothNormalizationOver V W) z) _ (sourceOpen_subset_smoothLocus V W z)

theorem targetToRegular_support :
    targetToRegular V W z ≫ Scheme.SmoothSupportOpen.Constructions.regularToSupport V.toOver
      (Image.Constructions.imageSupport V W z) = targetToSupport V W z :=
  Scheme.OpenSupportClosure.Constructions.smoothOpenToRegular_inclusion (Y := V.toOver)
    (Image.Constructions.imageSupport V W z) (targetToSupport V W z)

theorem targetToRegular_ambient :
    targetToRegular V W z ≫ Scheme.RegularSupport.Constructions.regularToAmbient V.toOver (Image.Constructions.imageSupport V W z) =
    targetToSupport V W z ≫ Scheme.RegularSupport.Constructions.supportToAmbient V.toOver (Image.Constructions.imageSupport V W z) := by
  rw [← Scheme.SmoothSupportOpen.Constructions.regularToSupport_ambient, ← Category.assoc, targetToRegular_support]

/-- The algebraic covering square still commutes after passage to the two
canonical regular loci and the original full ambient variety. -/
theorem regularCover_ambient_square :
    (sourceToRegular V W z ≫ Scheme.RegularSupport.Constructions.regularToAmbient (Normalization.AmbientMap.Constructions.smoothNormalizationOver V W)
      (SchemeDivisor.Purity.Constructions.primeSupport (Normalization.AmbientMap.Constructions.smoothNormalizationOver V W) z)) ≫ Normalization.PrincipalBoundary.Constructions.fullAmbientMap V W =
    Constructions.Etale.coverMap V W z ≫ (targetToRegular V W z ≫
      Scheme.RegularSupport.Constructions.regularToAmbient V.toOver (Image.Constructions.imageSupport V W z)) := by
  rw [sourceToRegular_ambient, targetToRegular_ambient]
  have h := ProperImage.AnalyticRestriction.Constructions.Construction.restrictedSchemeMap_inclusion (Map.finiteSupportMap V W z) (Constructions.Etale.goodOpen V W z)
  change Constructions.Etale.coverMap V W z ≫ ProperImage.AnalyticRestriction.Constructions.Construction.openSchemeInclusion (Map.openImageSupport V W z) (Constructions.Etale.goodOpen V W z) =
    ProperImage.AnalyticRestriction.Constructions.Construction.openSchemeInclusion (Map.sourceSupport V W z) ((Map.finiteSupportMap V W z).left ⁻¹ᵁ Constructions.Etale.goodOpen V W z) ≫
      Map.finiteSupportMap V W z at h
  rw [Category.assoc, ← Map.divisorMap_ambient, Map.divisorMap, targetToSupport,
    ← Category.assoc (Constructions.Etale.coverMap V W z), ← Category.assoc (Constructions.Etale.coverMap V W z), h]
  simp only [Category.assoc]

end Constructions.Regular

end

end OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationDivisor.Open
