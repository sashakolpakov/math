import OAI.AlgebraicGeometry.Divisors.LineBundles.Support.Projection
import OAI.AlgebraicGeometry.Divisors.LineBundles.Deformation.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType

/-! # Deformation Finite Type -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Global.DeformationFiniteType.BundleCycles

noncomputable section

/-!
# LineBundleCycles: finite type of the actual global deformation projections

The extended-Rees constants maps have finite type over Noetherian
coefficient rings. Source-locality transfers this property from the
constructed charts to the global projections.
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory
open _root_.AlgebraicGeometry.Scheme.AffineZariskiSite

universe u
variable {X : Scheme.{u}} [IsLocallyNoetherian X]

/-- The spectrum of the actual constants map has finite type. -/
theorem deformationConstants_locallyOfFiniteType {R : Type u} [CommRing R]
    [IsNoetherianRing R] (I : Ideal R) :
    LocallyOfFiniteType (Spec.map (CommRingCat.ofHom
      (algebraMap R (Deformation.Iff.BundleCycles.deformationAlgebra I)))) :=
  (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mpr
    (RingHom.finiteType_algebraMap.mpr
      (Deformation.FiniteType.BundleCycles.deformationAlgebra_finiteType I (IsNoetherian.noetherian I)))

/-- The global deformation projection is locally of finite type over a locally Noetherian base. -/
instance globalDeformationProjection_locallyOfFiniteType (I : X.IdealSheafData) :
    LocallyOfFiniteType (Deformation.BundleCycles.globalDeformationProjection I) := by
  let : IsZariskiLocalAtSource @LocallyOfFiniteType :=
    HasRingHomProperty.instIsZariskiLocalAtSource (Q := RingHom.FiniteType)
  apply IsZariskiLocalAtSource.of_openCover (P := @LocallyOfFiniteType) (Deformation.BundleCycles.globalDeformationCover I)
  intro U
  have : IsNoetherianRing Γ(X, U.1) := DeformationProperties.BundleCycles.affineBaseRing_noetherian U
  have hc := deformationConstants_locallyOfFiniteType (I.ideal U)
  have ht : LocallyOfFiniteType
      ((Deformation.BundleCycles.deformationGlueData I).natTrans.app U ≫ U.1.ι) := by
    change LocallyOfFiniteType ((Spec.map (CommRingCat.ofHom
      (algebraMap Γ(X, U.1) (Deformation.Iff.BundleCycles.deformationAlgebra (I.ideal U)))) ≫ U.2.isoSpec.inv) ≫ U.1.ι)
    infer_instance
  exact (congrArg (fun f => LocallyOfFiniteType f) ((Deformation.BundleCycles.deformationGlueData I).ι_toBase U)).mpr ht

/-- The projection to the actual closed support is locally of finite type. -/
instance globalSupportDeformationToSupport_locallyOfFiniteType (I P : X.IdealSheafData) :
    LocallyOfFiniteType (Support.Projection.BundleCycles.globalSupportDeformationToSupport I P) := by
  let : IsZariskiLocalAtSource @LocallyOfFiniteType :=
    HasRingHomProperty.instIsZariskiLocalAtSource (Q := RingHom.FiniteType)
  apply IsZariskiLocalAtSource.of_openCover (P := @LocallyOfFiniteType)
    (SupportDeformation.BundleCycles.globalSupportDeformationCover I P)
  intro U
  have : IsNoetherianRing Γ(X, U.1) := DeformationProperties.BundleCycles.affineBaseRing_noetherian U
  have : IsNoetherianRing ((Support.CoefficientDiagram.BundleCycles.supportCoefficientDiagram P).obj (.op U)) :=
    inferInstanceAs (IsNoetherianRing (Γ(X, U.1) ⧸ P.ideal U))
  have hc : LocallyOfFiniteType (Support.Projection.BundleCycles.supportDeformationChartProjection I P U) :=
    deformationConstants_locallyOfFiniteType (Support.CoefficientDiagram.BundleCycles.supportCenterIdeal P I U)
  have ho : IsOpenImmersion (Support.Projection.BundleCycles.supportCoefficientChart P U) :=
    Support.Projection.BundleCycles.supportCoefficientChart_isOpenImmersion P U
  have ht : LocallyOfFiniteType (Support.Projection.BundleCycles.supportDeformationChartToSupport I P U) :=
    @locallyOfFiniteType_comp _ _ _ (Support.Projection.BundleCycles.supportDeformationChartProjection I P U)
      (Support.Projection.BundleCycles.supportCoefficientChart P U) hc
      (@locallyOfFiniteType_of_isOpenImmersion _ _ (Support.Projection.BundleCycles.supportCoefficientChart P U) ho)
  exact (congrArg (fun f => LocallyOfFiniteType f)
    (Support.Projection.BundleCycles.globalSupportDeformationToSupport_on_chart I P U)).mpr ht

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Global.DeformationFiniteType.BundleCycles
