import OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.ScalarIndependence
import OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.PairedParameters

/-! # Data Scalar -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.DataScalar

noncomputable section

/-! The actual scalar of the fixed projective point class, expressed
from its full geometric parameter data. Paired frames on one ambient
open have the same original scalar, including its raw Koszul value. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.MvPolynomial
open OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.IntrinsicOverlap.Intrinsic OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.PairedParameters.ParameterChart
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {R : Type u} [CommRing R] [IsNoetherianRing R] [Module.Injective R R]
  [IsArtinianRing R] [IsLocalRing R] {n : ℕ}
attribute [local instance] MvPolynomial.gradedAlgebra
variable (X : Over (Spec (CommRingCat.of R))) (i : X ⟶ Projective.IntrinsicOverlap.Intrinsic.model R (n+1))
  [IsClosedImmersion i.left] [IsProper X.hom] [Smooth X.hom] [GeometricallyConnected X.hom]
  (z : Spec (CommRingCat.of R) ⟶ X.left) [IsClosedImmersion z]
  (hz : z ≫ X.hom = 𝟙 _) (g B : ℕ) (hB : n+2 ≤ B)
  (U : (Projective.IntrinsicOverlap.Intrinsic.space R (n+1)).Opens) (hU : IsAffineOpen U)

local instance composite_smooth : Smooth (i.left ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ) := by
  change Smooth (i.left ≫ (Projective.IntrinsicOverlap.Intrinsic.model R (n+1)).hom)
  rw [Over.w i]
  infer_instance
local instance composite_proper : IsProper (i.left ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ) := by
  change IsProper (i.left ≫ (Projective.IntrinsicOverlap.Intrinsic.model R (n+1)).hom)
  rw [Over.w i]
  infer_instance
local instance composite_connected : GeometricallyConnected (i.left ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ) := by
  change GeometricallyConnected (i.left ≫ (Projective.IntrinsicOverlap.Intrinsic.model R (n+1)).hom)
  rw [Over.w i]
  infer_instance

include hz in
omit [IsNoetherianRing R] [Module.Injective R R] [IsArtinianRing R] [IsLocalRing R] [IsClosedImmersion (Over.Hom.left i)] [IsProper X.hom] [Smooth X.hom] [GeometricallyConnected X.hom] [IsClosedImmersion z] in
theorem over_base : z ≫ (i.left ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ) = 𝟙 _ := by
  change z ≫ (i.left ≫ (Projective.IntrinsicOverlap.Intrinsic.model R (n+1)).hom) = _
  rw [Over.w i]
  exact hz

def value (D : PointParameterData.Chart.Data X i z g U hU) : R :=
  ScalarCoordinates.value i.left z (over_base X i z hz) B hB U hU D.contains
    D.coordinate D.below_coordinate
    (Projective.PrincipalResidueCoordinates.scalarFrame (c := n+1) (g := 0)
      (Survivor.chart (R := R)) U hU D.coordinate D.below_coordinate D.ambientBasis)
    D.equations D.parameters D.point_generates D.point_regular
    (LocalCoordinates.pointAt i.left z (over_base X i z hz) B hB U hU
      D.equations D.parameters D.point_generates D.dimension)

def rawValue (D : PointParameterData.Chart.Data X i z g U hU) : R :=
  ScalarCoordinates.rawValue i.left z (over_base X i z hz) B hB U hU D.contains
    D.coordinate D.below_coordinate
    (Projective.PrincipalResidueCoordinates.scalarFrame (c := n+1) (g := 0)
      (Survivor.chart (R := R)) U hU D.coordinate D.below_coordinate D.ambientBasis)
    D.equations D.parameters D.point_generates D.point_regular
    (LocalCoordinates.pointAt i.left z (over_base X i z hz) B hB U hU
      D.equations D.parameters D.point_generates D.dimension)

omit [IsArtinianRing R] [IsLocalRing R] [IsProper X.hom] [Smooth X.hom] [GeometricallyConnected X.hom] in
theorem value_eq_raw (D : PointParameterData.Chart.Data X i z g U hU) :
    value X i z hz g B hB U hU D = rawValue X i z hz g B hB U hU D :=
  ScalarCoordinates.value_eq_raw i.left z (over_base X i z hz) B hB U hU D.contains
    D.coordinate D.below_coordinate _ D.equations D.parameters D.point_generates D.point_regular _

omit [IsArtinianRing R] [IsLocalRing R] [IsProper X.hom] [Smooth X.hom] [GeometricallyConnected X.hom] in
theorem independent (D₁ D₂ : PointParameterData.Chart.Data X i z g U hU)
    (hcodimension : D₂.codimension = D₁.codimension) (hcoordinate : D₂.coordinate = D₁.coordinate) :
    value X i z hz g B hB U hU D₁ = value X i z hz g B hB U hU D₂ := by
  rcases D₁ with ⟨⟨k₁,hk₁,hc₁,c₁,hd₁,s₁,hs₁,hr₁,bI₁,hI₁,t₁,bQ₁,hQ₁,hst₁,hreg₁,τ₁,hτ₁,A₁,T₁,E₁⟩,b₁,hb₁⟩
  rcases D₂ with ⟨⟨k₂,hk₂,hc₂,c₂,hd₂,s₂,hs₂,hr₂,bI₂,hI₂,t₂,bQ₂,hQ₂,hst₂,hreg₂,τ₂,hτ₂,A₂,T₂,E₂⟩,b₂,hb₂⟩
  change c₂ = c₁ at hcodimension
  subst c₂
  change k₂ = k₁ at hcoordinate
  subst k₂
  exact ScalarIndependence.independent i.left z (over_base X i z hz) B hB U hU hc₁
    k₁ hk₁ hd₁ s₁ t₁ hst₁ hreg₁ b₁ hb₁ s₂ t₂ hst₂ hreg₂ b₂ hb₂

omit [IsArtinianRing R] [IsLocalRing R] [IsProper X.hom] [Smooth X.hom] [GeometricallyConnected X.hom] in
theorem raw_independent (D₁ D₂ : PointParameterData.Chart.Data X i z g U hU)
    (hcodimension : D₂.codimension = D₁.codimension) (hcoordinate : D₂.coordinate = D₁.coordinate) :
    rawValue X i z hz g B hB U hU D₁ = rawValue X i z hz g B hB U hU D₂ :=
  (value_eq_raw X i z hz g B hB U hU D₁).symm.trans
    ((independent X i z hz g B hB U hU D₁ D₂ hcodimension hcoordinate).trans
      (value_eq_raw X i z hz g B hB U hU D₂))

omit [IsArtinianRing R] [IsLocalRing R] [IsProper X.hom] [Smooth X.hom] [GeometricallyConnected X.hom] in
theorem paired (D : PointParameterData.Chart.Data X i z g U hU) (W : X.left.Opens)
    (t : Fin g → Intrinsic.SmoothClosedSections.ring R X W)
    (P : PairedParameters.ParameterChart.PairedData X i z g U hU D W t) :
    rawValue X i z hz g B hB P.ambient P.affine P.original =
      rawValue X i z hz g B hB P.ambient P.affine P.transported :=
  raw_independent X i z hz g B hB P.ambient P.affine P.original P.transported
    P.same_codimension P.same_coordinate

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.DataScalar
