import OAI.AlgebraicGeometry.Divisors.LineBundles.Conormal.DiagramGluing
import OAI.AlgebraicGeometry.Divisors.LineBundles.Relative.AffineMap
import OAI.AlgebraicGeometry.Divisors.LineBundles.Normal.ConeSymmetric

/-! # Normal Cone Embedding -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Global.NormalConeEmbedding.BundleCycles

noncomputable section

/-! # LineBundleCycles: the actual global normal cone embeds in the conormal symmetric spectrum -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry.Scheme.AffineZariskiSite

theorem normalConeSymmetricMap_special_base {R : Type} [CommRing R] (I : Ideal R) (r : R) :
    SpecialFiber.BundleCycles.normalConeSpecialFiberEquiv I (Normal.ConeSymmetric.BundleCycles.normalConeSymmetricMap I
      (algebraMap (R ⧸ I) (SymmetricAlgebra (R ⧸ I) I.Cotangent) (Ideal.Quotient.mk I r))) =
      Ideal.Quotient.mk (Deformation.Iff.BundleCycles.deformationSpecialIdeal I) (algebraMap R (Deformation.Iff.BundleCycles.deformationAlgebra I) r) := by
  rw [Normal.ConeSymmetric.BundleCycles.normalConeSymmetricMap_algebraMap, Normal.Cone.BundleCycles.normalConeBaseMap_mk, SpecialFiber.BundleCycles.normalConeSpecialFiberEquiv_mk]
  exact congrArg (Ideal.Quotient.mk _) ((Deformation.Iff.BundleCycles.reesToDeformation I).commutes r)

variable {X : Scheme.{0}} (I : X.IdealSheafData)

theorem conormalSymmetricToSpecialDiagram_base :
    Conormal.SymmetricDiagram.BundleCycles.conormalSymmetricDiagramMap I ≫ Conormal.SymmetricDiagram.BundleCycles.conormalSymmetricToSpecialDiagram I = SpecialFiber.BundleCycles.specialFiberDiagramMap I := by
  apply NatTrans.ext
  funext U
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro r
  exact normalConeSymmetricMap_special_base (I.ideal U.unop) r

theorem conormalSymmetricToSpecialDiagram_surjective (U : X.AffineZariskiSite) :
    Function.Surjective ((Conormal.SymmetricDiagram.BundleCycles.conormalSymmetricToSpecialDiagram I).app (.op U)) :=
  (SpecialFiber.BundleCycles.normalConeSpecialFiberEquiv (I.ideal U)).surjective.comp (Normal.ConeSymmetric.BundleCycles.normalConeSymmetricMap_surjective (I.ideal U))

def globalNormalConeToConormal : SpecialFiber.BundleCycles.globalSpecialFiber I ⟶ Conormal.DiagramGluing.BundleCycles.globalConormalSpectrum I :=
  Relative.AffineMap.BundleCycles.relativeAffineMap (Conormal.DiagramGluing.BundleCycles.conormalSymmetricDiagramMap_coequifibered I)
    (SpecialFiber.BundleCycles.specialFiberDiagramMap_coequifibered I) (Conormal.SymmetricDiagram.BundleCycles.conormalSymmetricToSpecialDiagram I)

theorem globalNormalConeToConormal_on_chart (U : X.AffineZariskiSite) :
    (SpecialFiber.BundleCycles.globalSpecialFiberCover I).f U ≫ globalNormalConeToConormal I =
      Spec.map ((Conormal.SymmetricDiagram.BundleCycles.conormalSymmetricToSpecialDiagram I).app (.op U)) ≫ (Conormal.DiagramGluing.BundleCycles.globalConormalSpectrumCover I).f U :=
  Relative.AffineMap.BundleCycles.relativeAffineMap_on_chart (Conormal.DiagramGluing.BundleCycles.conormalSymmetricDiagramMap_coequifibered I)
    (SpecialFiber.BundleCycles.specialFiberDiagramMap_coequifibered I) (Conormal.SymmetricDiagram.BundleCycles.conormalSymmetricToSpecialDiagram I) U

theorem globalNormalConeToConormal_toBase :
    globalNormalConeToConormal I ≫ Conormal.DiagramGluing.BundleCycles.globalConormalSpectrumProjection I = SpecialFiber.BundleCycles.globalSpecialFiberProjection I :=
  Relative.AffineMap.BundleCycles.relativeAffineMap_toBase (Conormal.DiagramGluing.BundleCycles.conormalSymmetricDiagramMap_coequifibered I)
    (SpecialFiber.BundleCycles.specialFiberDiagramMap_coequifibered I) (Conormal.SymmetricDiagram.BundleCycles.conormalSymmetricToSpecialDiagram I)
    (conormalSymmetricToSpecialDiagram_base I)

theorem globalNormalConeToConormal_chart_isPullback (U : X.AffineZariskiSite) :
    IsPullback (Spec.map ((Conormal.SymmetricDiagram.BundleCycles.conormalSymmetricToSpecialDiagram I).app (.op U)))
      ((SpecialFiber.BundleCycles.globalSpecialFiberCover I).f U) ((Conormal.DiagramGluing.BundleCycles.globalConormalSpectrumCover I).f U) (globalNormalConeToConormal I) :=
  Relative.AffineMap.BundleCycles.relativeAffineMap_chart_isPullback (Conormal.DiagramGluing.BundleCycles.conormalSymmetricDiagramMap_coequifibered I)
    (SpecialFiber.BundleCycles.specialFiberDiagramMap_coequifibered I) (Conormal.SymmetricDiagram.BundleCycles.conormalSymmetricToSpecialDiagram I)
    (conormalSymmetricToSpecialDiagram_base I) U

instance globalNormalConeToConormal_isClosedImmersion : IsClosedImmersion (globalNormalConeToConormal I) :=
  Relative.AffineMap.BundleCycles.relativeAffineMap_isClosedImmersion (Conormal.DiagramGluing.BundleCycles.conormalSymmetricDiagramMap_coequifibered I)
    (SpecialFiber.BundleCycles.specialFiberDiagramMap_coequifibered I) (Conormal.SymmetricDiagram.BundleCycles.conormalSymmetricToSpecialDiagram I)
    (conormalSymmetricToSpecialDiagram_base I) (conormalSymmetricToSpecialDiagram_surjective I)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Global.NormalConeEmbedding.BundleCycles
