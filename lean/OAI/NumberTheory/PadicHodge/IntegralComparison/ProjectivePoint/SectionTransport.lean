import OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.PointParameterData

/-! # Section Transport -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint

noncomputable section

/-! Replacing a section by an equal morphism preserves every parameter
and every chosen basis of the same projective point chart. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.MvPolynomial
open OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.IntrinsicOverlap.Intrinsic
universe u
variable {R : Type u} [CommRing R] [IsNoetherianRing R] {N : ℕ}
attribute [local instance] MvPolynomial.gradedAlgebra
variable (X : Over (Spec (CommRingCat.of R))) (f : X ⟶ Projective.IntrinsicOverlap.Intrinsic.model R N)
  [IsClosedImmersion f.left] {z z' : Spec (CommRingCat.of R) ⟶ X.left}
  (g : ℕ) (U : (Projective.IntrinsicOverlap.Intrinsic.space R N).Opens) (hU : IsAffineOpen U) (h : z = z')

def PointParameterData.Chart.ParameterData.changeSection (D : PointParameterData.Chart.ParameterData X f z g U hU) :
    PointParameterData.Chart.ParameterData X f z' g U hU :=
  { D with
    contains := by simpa only [← h] using D.contains
    point_generates := by simpa only [← h] using D.point_generates }

def PointParameterData.Chart.Data.changeSection (D : PointParameterData.Chart.Data X f z g U hU) : PointParameterData.Chart.Data X f z' g U hU :=
  { toParameterData := D.toParameterData.changeSection X f g U hU h
    ambientBasis := D.ambientBasis
    ambientBasis_apply := D.ambientBasis_apply }

omit [IsNoetherianRing R] [IsClosedImmersion (Over.Hom.left f)] in
@[simp] theorem PointParameterData.Chart.ParameterData.changeSection_rfl (D : PointParameterData.Chart.ParameterData X f z g U hU) :
    D.changeSection X f g U hU rfl = D := rfl

omit [IsNoetherianRing R] [IsClosedImmersion (Over.Hom.left f)] in
@[simp] theorem PointParameterData.Chart.Data.changeSection_rfl (D : PointParameterData.Chart.Data X f z g U hU) :
    D.changeSection X f g U hU rfl = D := rfl

omit [IsNoetherianRing R] [IsClosedImmersion (Over.Hom.left f)] in
@[simp] theorem PointParameterData.Chart.Data.changeSection_codimension (D : PointParameterData.Chart.Data X f z g U hU) :
    (D.changeSection X f g U hU h).codimension = D.codimension := rfl

omit [IsNoetherianRing R] [IsClosedImmersion (Over.Hom.left f)] in
@[simp] theorem PointParameterData.Chart.Data.changeSection_coordinate (D : PointParameterData.Chart.Data X f z g U hU) :
    (D.changeSection X f g U hU h).coordinate = D.coordinate := rfl

omit [IsNoetherianRing R] [IsClosedImmersion (Over.Hom.left f)] in
@[simp] theorem PointParameterData.Chart.Data.changeSection_equations (D : PointParameterData.Chart.Data X f z g U hU) :
    (D.changeSection X f g U hU h).equations = D.equations := rfl

omit [IsNoetherianRing R] [IsClosedImmersion (Over.Hom.left f)] in
@[simp] theorem PointParameterData.Chart.Data.changeSection_parameters (D : PointParameterData.Chart.Data X f z g U hU) :
    (D.changeSection X f g U hU h).parameters = D.parameters := rfl

omit [IsNoetherianRing R] [IsClosedImmersion (Over.Hom.left f)] in
@[simp] theorem PointParameterData.Chart.Data.changeSection_ambientBasis (D : PointParameterData.Chart.Data X f z g U hU) :
    (D.changeSection X f g U hU h).ambientBasis = D.ambientBasis := rfl

omit [IsNoetherianRing R] [IsClosedImmersion (Over.Hom.left f)] in
@[simp] theorem PointParameterData.Chart.Data.changeSection_conormalBasis (D : PointParameterData.Chart.Data X f z g U hU) :
    (D.changeSection X f g U hU h).conormalBasis = D.conormalBasis := rfl

omit [IsNoetherianRing R] [IsClosedImmersion (Over.Hom.left f)] in
@[simp] theorem PointParameterData.Chart.Data.changeSection_quotientBasis (D : PointParameterData.Chart.Data X f z g U hU) :
    (D.changeSection X f g U hU h).quotientBasis = D.quotientBasis := rfl

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint
