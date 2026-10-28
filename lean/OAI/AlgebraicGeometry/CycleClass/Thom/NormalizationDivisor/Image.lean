import OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.PrincipalBoundary
import OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.OpenSupportClosure
import OAI.AlgebraicGeometry.CycleClass.Thom.Integral.MapDimension

/-! # Image -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationDivisor.Image

noncomputable section

/-! Every actual prime divisor on the smooth normalization defines its
actual reduced ambient image in precisely the ThomClass principal-divisor degree. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Constructions

open OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.AmbientMap.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.AmbientTopology.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.PrincipalBoundary.Constructions
  SchemeDivisor.Purity.Constructions Scheme.RegularSupport.Constructions

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (W : IrreducibleCloseds V.carrier)

local instance : AlgebraicGeometry.IsNoetherian V.carrier := Foundations.Scheme.ClosedProjective.isNoetherian_of_isProper_toSpec V.structureMap
local instance : Smooth (Normalization.AmbientMap.Constructions.smoothNormalizationOver V W).hom := Normalization.AmbientMap.Constructions.smoothNormalization_smooth V W
local instance : IsFinite (Normalization.AmbientMap.Constructions.smoothNormalizationToAmbient V W).left := Normalization.AmbientMap.Constructions.smoothNormalization_finite V W
local instance : QuasiCompact (ProperImage.AnalyticRestriction.Constructions.Construction.openSchemeInclusion V.toOver (Normalization.AmbientMap.Constructions.ambientOpen V W)).left :=
  inferInstanceAs (QuasiCompact (Normalization.AmbientMap.Constructions.ambientOpen V W).ι)

/-- The original finite image in the ambient open, followed by its actual
reduced closure in the given projective variety. -/
def imageSupport (z : {x : (Normalization.AmbientMap.Constructions.smoothNormalizationOver V W).left // Order.coheight x = 1}) :
    IrreducibleCloseds V.carrier :=
  Scheme.OpenSupportClosure.Constructions.closureSupport
    (ProperImage.AnalyticRestriction.Constructions.Construction.openSchemeInclusion V.toOver (Normalization.AmbientMap.Constructions.ambientOpen V W))
    (Scheme.ProperSupport.Constructions.imageSupport (Normalization.AmbientMap.Constructions.smoothNormalizationToAmbient V W)
      (SchemeDivisor.Purity.Constructions.primeSupport (Normalization.AmbientMap.Constructions.smoothNormalizationOver V W) z))

theorem imageSupport_dimension (z : {x : (Normalization.AmbientMap.Constructions.smoothNormalizationOver V W).left // Order.coheight x = 1}) :
    Foundations.Scheme.SupportDimension.supportTranscendenceDimension (imageSupport V W z) V.structureMap + 1 =
      Foundations.Scheme.SupportDimension.supportTranscendenceDimension W V.structureMap := by
  have hc := Scheme.OpenSupportClosure.Constructions.closureSupport_dimension
    (ProperImage.AnalyticRestriction.Constructions.Construction.openSchemeInclusion V.toOver (Normalization.AmbientMap.Constructions.ambientOpen V W))
    (Scheme.ProperSupport.Constructions.imageSupport (Normalization.AmbientMap.Constructions.smoothNormalizationToAmbient V W)
      (SchemeDivisor.Purity.Constructions.primeSupport (Normalization.AmbientMap.Constructions.smoothNormalizationOver V W) z))
  have hf := Integral.MapDimension.Constructions.finite_support_dimension (Normalization.AmbientMap.Constructions.smoothNormalizationToAmbient V W)
    (SchemeDivisor.Purity.Constructions.primeSupport (Normalization.AmbientMap.Constructions.smoothNormalizationOver V W) z)
  have hs := SchemeDivisor.Purity.Constructions.primeRegularDimension_add_one (Normalization.AmbientMap.Constructions.smoothNormalizationOver V W) z
  rw [Scheme.RegularSupport.Constructions.regularDimension_eq] at hs
  rw [← Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension_eq_functionFieldDifferentialDimension,
    Normalization.AmbientTopology.Constructions.smoothNormalization_dimension] at hs
  exact (congrArg (fun d => d + 1) (hc.trans hf)).trans hs

theorem imageSupport_codimension (z : {x : (Normalization.AmbientMap.Constructions.smoothNormalizationOver V W).left // Order.coheight x = 1}) :
    Geometric.DimensionCycles.dimensionCodimension V (imageSupport V W z) = Geometric.DimensionCycles.dimensionCodimension V W + 1 := by
  have hz := imageSupport_dimension V W z
  have hi := Geometric.DimensionCycles.supportDimension_add_dimensionCodimension V (imageSupport V W z)
  have hw := Geometric.DimensionCycles.supportDimension_add_dimensionCodimension V W
  omega

/-- The genuine image support, in its proved ambient principal-divisor codimension. -/
def imageCycleSupport (z : {x : (Normalization.AmbientMap.Constructions.smoothNormalizationOver V W).left // Order.coheight x = 1}) :
    Geometric.DimensionCycles.DimensionCycleSupport V (Geometric.DimensionCycles.dimensionCodimension V W + 1) :=
  ⟨imageSupport V W z, imageSupport_codimension V W z⟩

theorem imageSupport_genericPoint (z : {x : (Normalization.AmbientMap.Constructions.smoothNormalizationOver V W).left // Order.coheight x = 1}) :
    irreducibleSetEquivPoints (imageSupport V W z) = (Normalization.PrincipalBoundary.Constructions.fullAmbientMap V W).left z.val := by
  have hc := Scheme.OpenSupportClosure.Constructions.closureSupport_genericPoint
    (ProperImage.AnalyticRestriction.Constructions.Construction.openSchemeInclusion V.toOver (Normalization.AmbientMap.Constructions.ambientOpen V W))
    (Scheme.ProperSupport.Constructions.imageSupport (Normalization.AmbientMap.Constructions.smoothNormalizationToAmbient V W)
      (SchemeDivisor.Purity.Constructions.primeSupport (Normalization.AmbientMap.Constructions.smoothNormalizationOver V W) z))
  have hf := Scheme.ProperSupport.Constructions.imageSupport_genericPoint (Normalization.AmbientMap.Constructions.smoothNormalizationToAmbient V W)
    (SchemeDivisor.Purity.Constructions.primeSupport (Normalization.AmbientMap.Constructions.smoothNormalizationOver V W) z)
  rw [hf] at hc
  change irreducibleSetEquivPoints
    (Scheme.OpenSupportClosure.Constructions.closureSupport (ProperImage.AnalyticRestriction.Constructions.Construction.openSchemeInclusion V.toOver (Normalization.AmbientMap.Constructions.ambientOpen V W))
      (Scheme.ProperSupport.Constructions.imageSupport (Normalization.AmbientMap.Constructions.smoothNormalizationToAmbient V W)
        (SchemeDivisor.Purity.Constructions.primeSupport (Normalization.AmbientMap.Constructions.smoothNormalizationOver V W) z))) =
    (ProperImage.AnalyticRestriction.Constructions.Construction.openSchemeInclusion V.toOver (Normalization.AmbientMap.Constructions.ambientOpen V W)).left ((Normalization.AmbientMap.Constructions.smoothNormalizationToAmbient V W).left z.val)
  simpa only [SchemeDivisor.Purity.Constructions.primeSupport, OrderIso.apply_symm_apply] using hc

/-- The residue degree is unchanged by reinserting the actual ambient open. -/
theorem image_residueDegree (z : {x : (Normalization.AmbientMap.Constructions.smoothNormalizationOver V W).left // Order.coheight x = 1}) :
    (Normalization.AmbientMap.Constructions.smoothNormalizationToAmbient V W).left.residueDegree z.val =
      (Normalization.PrincipalBoundary.Constructions.fullAmbientMap V W).left.residueDegree z.val :=
  (ProperImage.ResidueDegree.Constructions.Construction.residueDegree_post_immersion (Normalization.AmbientMap.Constructions.smoothNormalizationToAmbient V W).left
    (ProperImage.AnalyticRestriction.Constructions.Construction.openSchemeInclusion V.toOver (Normalization.AmbientMap.Constructions.ambientOpen V W)).left z.val).symm

end Constructions

end

end OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationDivisor.Image
