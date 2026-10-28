import OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.SectionTransport
import OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.DataScalar

/-! # Section Transport Scalar -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.SectionTransportScalar.Data

noncomputable section

/-! The original projective point scalar is unchanged when its section
is replaced by an equal morphism, with all chart data retained. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.MvPolynomial
open OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.IntrinsicOverlap.Intrinsic
universe u
variable {R : Type u} [CommRing R] [IsNoetherianRing R] [Module.Injective R R]
  [IsArtinianRing R] [IsLocalRing R] {n : ℕ}
attribute [local instance] MvPolynomial.gradedAlgebra
variable (X : Over (Spec (CommRingCat.of R))) (i : X ⟶ Projective.IntrinsicOverlap.Intrinsic.model R (n+1))
  [IsClosedImmersion i.left] [IsProper X.hom] [Smooth X.hom] [GeometricallyConnected X.hom]
  {z z' : Spec (CommRingCat.of R) ⟶ X.left} [IsClosedImmersion z] [IsClosedImmersion z']
  (hz : z ≫ X.hom = 𝟙 _) (hz' : z' ≫ X.hom = 𝟙 _)
  (g B : ℕ) (hB : n+2 ≤ B) (U : (Projective.IntrinsicOverlap.Intrinsic.space R (n+1)).Opens) (hU : IsAffineOpen U)
  (h : z = z') (D : PointParameterData.Chart.Data X i z g U hU)

omit [IsArtinianRing R] [IsLocalRing R] [IsProper X.hom] [Smooth X.hom] [GeometricallyConnected X.hom] in
theorem value_changeSection :
    DataScalar.value X i z' hz' g B hB U hU (D.changeSection X i g U hU h) =
      DataScalar.value X i z hz g B hB U hU D := by
  subst z'
  rfl

omit [IsArtinianRing R] [IsLocalRing R] [IsProper X.hom] [Smooth X.hom] [GeometricallyConnected X.hom] in
theorem rawValue_changeSection :
    DataScalar.rawValue X i z' hz' g B hB U hU (D.changeSection X i g U hU h) =
      DataScalar.rawValue X i z hz g B hB U hU D := by
  subst z'
  rfl

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.SectionTransportScalar.Data
