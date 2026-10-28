import OAI.AlgebraicGeometry.Resolution.Blowups.Quotient.PointedOpenSmoothness
import OAI.AlgebraicGeometry.Resolution.Blowups.Global.CanonicalBoundaryAtlas
import OAI.AlgebraicGeometry.Resolution.Blowups.Global.SmoothCenterBlowup

/-! # Mixed Center Smoothness -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups

noncomputable section

/-! Common boundary-center coordinates prove smoothness of the actual center and global blowup. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u v

theorem MixedBoundary.CenterCharts.Construction.HasMixedBoundaryCenterCharts.smooth
    {k : Type u} [Field k] {R : CommRingCat.{u}} [Algebra k R]
    (I : Ideal R) {ι : Type v} {w : ι → R} {F : Finset ι}
    (h : MixedBoundary.CenterCharts.Construction.HasMixedBoundaryCenterCharts k R I w F) : Algebra.Smooth k (R ⧸ I) := by
  apply Quotient.PointedOpenSmoothness.Construction.smooth_quotient_of_pointed_open_charts k I
  intro p hp
  obtain ⟨C⟩ := h p hp
  refine ⟨C.chart.carrier, inferInstance, C.chart.map, inferInstance,
    C.chart.point, C.chart.point_over, ?_⟩
  rw [C.center_eq]
  let M := C.chart.model
  let : Algebra (MvPolynomial M.indices k) C.chart.carrier := M.map.toAlgebra
  let : Algebra.Etale (MvPolynomial M.indices k) C.chart.carrier :=
    RingHom.etale_algebraMap.mp M.etale
  let : IsScalarTower k (MvPolynomial M.indices k) C.chart.carrier :=
    IsScalarTower.of_algebraMap_eq (fun x => (M.ground x).symm)
  exact Blowups.Etale.Monomial.Construction.etaleSubsetCoordinateCenter_smooth (R := k) (S := C.chart.carrier) C.coordinates

theorem Global.CanonicalBoundaryAtlas.Construction.GlobalMixedCenterAtlas.center_smooth
    {X : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {I : X.IdealSheafData}
    {β : Type} {D : β → X.IdealSheafData} (A : Global.CanonicalBoundaryAtlas.Construction.GlobalMixedCenterAtlas f I D) :
    Smooth (I.subschemeι ≫ f) := by
  apply Global.MonomialBoundaryAtlas.Construction.idealSheaf_complex_center_smooth_of_chosen_affine_cover f I A.opens A.cover
  intro i
  let : Algebra ℂ Γ(X, A.opens i) := Blowups.Smooth.DifferentialIdealSheaf.Construction.affineComplexAlgebra f (A.opens i)
  exact (A.center i).smooth (I.ideal (A.opens i))

theorem Global.CanonicalBoundaryAtlas.Construction.GlobalMixedCenterAtlas.ambient_smooth
    {X : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {I : X.IdealSheafData}
    {β : Type} {D : β → X.IdealSheafData} (A : Global.CanonicalBoundaryAtlas.Construction.GlobalMixedCenterAtlas f I D) : Smooth f := by
  let : IsZariskiLocalAtSource @AlgebraicGeometry.Smooth :=
    HasRingHomProperty.instIsZariskiLocalAtSource (Q := @RingHom.Smooth)
  apply IsZariskiLocalAtSource.of_openCover (P := @Smooth) (Global.MonomialBoundaryAtlas.Construction.chosenAffineSpecCover A.opens A.cover).openCover
  intro i
  change Smooth ((A.opens i).2.fromSpec ≫ f)
  rw [← Affine.ComplexNaturality.Construction.affineComplexScalars_spec f (A.opens i)]
  let : Algebra ℂ Γ(X, A.opens i) := Blowups.Smooth.DifferentialIdealSheaf.Construction.affineComplexAlgebra f (A.opens i)
  exact (HasRingHomProperty.Spec_iff (P := @Smooth)).mpr
    (RingHom.smooth_algebraMap.mpr (A.boundary i).smooth)

theorem Global.CanonicalBoundaryAtlas.Construction.GlobalMixedCenterAtlas.blowup_smooth
    {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X]
    {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {I : X.IdealSheafData}
    {β : Type} {D : β → X.IdealSheafData} (A : Global.CanonicalBoundaryAtlas.Construction.GlobalMixedCenterAtlas f I D) (hI : I ≠ ⊥) :
    Smooth (GlobalBlowup.Data.Construction.globalBlowupToBase I hI ≫ f) := by
  let : Smooth f := A.ambient_smooth
  let : Smooth (I.subschemeι ≫ f) := A.center_smooth
  exact Global.SmoothCenterBlowup.Construction.globalBlowup_smooth_of_smooth_center f I hI

end

end OAI.AlgebraicGeometry.Resolution.Blowups
