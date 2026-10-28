import OAI.AlgebraicGeometry.Divisors.LineBundles.Support.DeformationDiagram
import OAI.AlgebraicGeometry.Divisors.LineBundles.Global.DeformationProperties
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType

/-! # Support Deformation -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Global.SupportDeformation.BundleCycles

noncomputable section

/-!
# LineBundleCycles: the global deformation of a closed support

The affine extended-Rees algebras over the actual support quotients glue
to a scheme. The coefficient quotient maps give a closed immersion into
the ambient deformation, with the expected affine restrictions.
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry.Scheme.AffineZariskiSite

universe u
variable {X : Scheme.{u}} (I P : X.IdealSheafData)

def supportDeformationGlueData : (directedCover X).RelativeGluingData :=
  relativeGluingData (Support.DeformationDiagram.BundleCycles.supportDeformationDiagramMap_coequifibered I P)

instance supportDeformationGlueData_isLocallyDirected :
    ((supportDeformationGlueData I P).functor ⋙ Scheme.forget).IsLocallyDirected :=
  Scheme.Cover.RelativeGluingData.instIsLocallyDirectedI₀CompFunctorForgetOfIsThin ..

/-- The global deformation of the closed support with its restricted center. -/
def globalSupportDeformation : Scheme := (supportDeformationGlueData I P).glued

def globalSupportDeformationCover : (globalSupportDeformation I P).OpenCover :=
  (supportDeformationGlueData I P).cover

def globalSupportDeformationProjection : globalSupportDeformation I P ⟶ X :=
  (supportDeformationGlueData I P).toBase

/-- The actual global map induced by quotienting the ambient coefficients. -/
def globalSupportDeformationMap : globalSupportDeformation I P ⟶ Deformation.BundleCycles.globalDeformation I :=
  Relative.AffineMap.BundleCycles.relativeAffineMap (Deformation.BundleCycles.deformationDiagramMap_coequifibered I)
    (Support.DeformationDiagram.BundleCycles.supportDeformationDiagramMap_coequifibered I P) (Support.DeformationDiagram.BundleCycles.deformationToSupportDiagram I P)

theorem globalSupportDeformationMap_on_chart (U : X.AffineZariskiSite) :
    (globalSupportDeformationCover I P).f U ≫ globalSupportDeformationMap I P =
      Deformation.ClosedSupport.BundleCycles.closedSupportDeformationInclusion (I.ideal U) (P.ideal U) ≫ (Deformation.BundleCycles.globalDeformationCover I).f U :=
  Relative.AffineMap.BundleCycles.relativeAffineMap_on_chart (Deformation.BundleCycles.deformationDiagramMap_coequifibered I)
    (Support.DeformationDiagram.BundleCycles.supportDeformationDiagramMap_coequifibered I P) (Support.DeformationDiagram.BundleCycles.deformationToSupportDiagram I P) U

theorem globalSupportDeformationMap_toBase :
    globalSupportDeformationMap I P ≫ Deformation.BundleCycles.globalDeformationProjection I =
      globalSupportDeformationProjection I P :=
  Relative.AffineMap.BundleCycles.relativeAffineMap_toBase (Deformation.BundleCycles.deformationDiagramMap_coequifibered I)
    (Support.DeformationDiagram.BundleCycles.supportDeformationDiagramMap_coequifibered I P) (Support.DeformationDiagram.BundleCycles.deformationToSupportDiagram I P) rfl

theorem globalSupportDeformationMap_chart_isPullback (U : X.AffineZariskiSite) :
    IsPullback (Deformation.ClosedSupport.BundleCycles.closedSupportDeformationInclusion (I.ideal U) (P.ideal U))
      ((globalSupportDeformationCover I P).f U) ((Deformation.BundleCycles.globalDeformationCover I).f U)
      (globalSupportDeformationMap I P) :=
  Relative.AffineMap.BundleCycles.relativeAffineMap_chart_isPullback (Deformation.BundleCycles.deformationDiagramMap_coequifibered I)
    (Support.DeformationDiagram.BundleCycles.supportDeformationDiagramMap_coequifibered I P) (Support.DeformationDiagram.BundleCycles.deformationToSupportDiagram I P) rfl U

/-- Deformation of a closed support remains a closed subscheme of the ambient deformation. -/
instance globalSupportDeformationMap_isClosedImmersion :
    IsClosedImmersion (globalSupportDeformationMap I P) :=
  Relative.AffineMap.BundleCycles.relativeAffineMap_isClosedImmersion (Deformation.BundleCycles.deformationDiagramMap_coequifibered I)
    (Support.DeformationDiagram.BundleCycles.supportDeformationDiagramMap_coequifibered I P) (Support.DeformationDiagram.BundleCycles.deformationToSupportDiagram I P) rfl
    (Support.DeformationDiagram.BundleCycles.deformationToSupportDiagram_surjective I P)

instance globalSupportDeformationCover_isOpenImmersion (U : X.AffineZariskiSite) :
    IsOpenImmersion ((globalSupportDeformationCover I P).f U) :=
  (globalSupportDeformationCover I P).map_prop U

theorem globalSupportDeformationProjection_preimage (U : X.AffineZariskiSite) :
    globalSupportDeformationProjection I P ⁻¹ᵁ U.1 =
      ((globalSupportDeformationCover I P).f U).opensRange := by
  have h := (supportDeformationGlueData I P).toBase_preimage_eq_opensRange_ι U
  change globalSupportDeformationProjection I P ⁻¹ᵁ U.1.ι.opensRange =
    ((globalSupportDeformationCover I P).f U).opensRange at h
  rw [Scheme.Opens.opensRange_ι] at h
  exact h

/-- The support deformation is Noetherian when the ambient base is Noetherian. -/
instance globalSupportDeformation_isNoetherian [AlgebraicGeometry.IsNoetherian X] :
    AlgebraicGeometry.IsNoetherian (globalSupportDeformation I P) := by
  have : IsLocallyNoetherian (globalSupportDeformation I P) :=
    LocallyOfFiniteType.isLocallyNoetherian (globalSupportDeformationMap I P)
  have : CompactSpace (globalSupportDeformation I P) :=
    QuasiCompact.compactSpace_of_compactSpace (globalSupportDeformationMap I P)
  exact ⟨⟩

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Global.SupportDeformation.BundleCycles
