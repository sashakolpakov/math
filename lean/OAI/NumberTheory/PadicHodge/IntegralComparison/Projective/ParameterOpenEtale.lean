import OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.PointParameterData
import OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.EtaleCoordinateRestriction
import OAI.NumberTheory.PadicHodge.IntegralComparison.AffineOpen.DeRhamTrace

/-! # Parameter Open Etale -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.ParameterOpenEtale

noncomputable section

/-! The polynomial étale coordinates of an actual projective point
chart restrict to an arbitrary affine subopen, also after finite
étale pullback. No new coordinate choice is assumed. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.MvPolynomial
open OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.IntrinsicOverlap.Intrinsic
universe u
variable {R : Type u} [CommRing R] [IsNoetherianRing R] {n : ℕ}
attribute [local instance] MvPolynomial.gradedAlgebra
variable (X : Over (Spec (CommRingCat.of R)))
  (i : X ⟶ IntrinsicOverlap.Intrinsic.model R n) [IsClosedImmersion i.left]
  (s : Spec (CommRingCat.of R) ⟶ X.left) (g : ℕ)
  (U : (IntrinsicOverlap.Intrinsic.space R n).Opens) (hU : IsAffineOpen U)
  (D : ProjectivePoint.PointParameterData.Chart.ParameterData X i s g U hU)

section Target
variable (V : X.left.Opens) (hV : IsAffineOpen V) (hVU : V ≤ i.left ⁻¹ᵁ U)

@[instance_reducible]
def openAlgebra : Algebra (MvPolynomial D.coordinateIndex R) (IntrinsicDeRham.SectionUnit.Intrinsic.ring R X V) := by
  letI := D.coordinates
  letI := D.coordinateTower
  exact Affine.EtaleCoordinateRestriction.algebra R X (homOfLE hVU) D.coordinateIndex

omit [IsNoetherianRing R] [IsClosedImmersion i.left] in
theorem openTower : letI := openAlgebra X i s g U hU D V hVU
    IsScalarTower R (MvPolynomial D.coordinateIndex R) (IntrinsicDeRham.SectionUnit.Intrinsic.ring R X V) := by
  let := D.coordinates
  let := D.coordinateTower
  exact Affine.EtaleCoordinateRestriction.tower R X (homOfLE hVU) D.coordinateIndex

include hV in
omit [IsNoetherianRing R] in
theorem openEtale : letI := openAlgebra X i s g U hU D V hVU
    Algebra.Etale (MvPolynomial D.coordinateIndex R) (IntrinsicDeRham.SectionUnit.Intrinsic.ring R X V) := by
  let := D.coordinates
  let := D.coordinateTower
  let := D.coordinateEtale
  exact Affine.EtaleCoordinateRestriction.etale R X (homOfLE hVU) D.coordinateIndex
    (hU.preimage i.left) hV
end Target

variable (Y : Over (Spec (CommRingCat.of R))) (f : Y ⟶ X)
  [IsFinite f.left] [Etale f.left]
  (V : Y.left.Opens) (hV : IsAffineOpen V) (hVU : V ≤ f.left ⁻¹ᵁ (i.left ⁻¹ᵁ U))

@[instance_reducible]
private def coordinateOrder : LinearOrder D.coordinateIndex := by
  letI := D.finiteVariables
  exact LinearOrder.lift' (Fintype.equivFin D.coordinateIndex) (Fintype.equivFin D.coordinateIndex).injective

@[instance_reducible]
def sourceAlgebra : Algebra (MvPolynomial D.coordinateIndex R) (IntrinsicDeRham.SectionUnit.Intrinsic.ring R Y V) := by
  letI := D.coordinates
  letI := D.coordinateTower
  letI := D.coordinateEtale
  letI := D.finiteVariables
  letI := coordinateOrder X i s g U hU D
  letI : Fact (IsAffineOpen (i.left ⁻¹ᵁ U)) := ⟨hU.preimage i.left⟩
  letI := AffineOpen.DeRhamTrace.polynomialSource R Y X f (i.left ⁻¹ᵁ U) D.coordinateIndex
  letI := AffineOpen.DeRhamTrace.polynomialBaseTower R Y X f (i.left ⁻¹ᵁ U) D.coordinateIndex
  exact Affine.EtaleCoordinateRestriction.algebra R Y (homOfLE hVU) D.coordinateIndex

omit [IsNoetherianRing R] in
omit [IsFinite (Over.Hom.left f)] [Etale (Over.Hom.left f)] in
theorem sourceTower : letI := sourceAlgebra X i s g U hU D Y f V hVU
    IsScalarTower R (MvPolynomial D.coordinateIndex R) (IntrinsicDeRham.SectionUnit.Intrinsic.ring R Y V) := by
  let := D.coordinates
  let := D.coordinateTower
  let := D.coordinateEtale
  let := D.finiteVariables
  let := coordinateOrder X i s g U hU D
  let : Fact (IsAffineOpen (i.left ⁻¹ᵁ U)) := ⟨hU.preimage i.left⟩
  let := AffineOpen.DeRhamTrace.polynomialSource R Y X f (i.left ⁻¹ᵁ U) D.coordinateIndex
  let := AffineOpen.DeRhamTrace.polynomialBaseTower R Y X f (i.left ⁻¹ᵁ U) D.coordinateIndex
  exact Affine.EtaleCoordinateRestriction.tower R Y (homOfLE hVU) D.coordinateIndex

include hV in
omit [IsNoetherianRing R] in
theorem sourceEtale : letI := sourceAlgebra X i s g U hU D Y f V hVU
    Algebra.Etale (MvPolynomial D.coordinateIndex R) (IntrinsicDeRham.SectionUnit.Intrinsic.ring R Y V) := by
  let := D.coordinates
  let := D.coordinateTower
  let := D.coordinateEtale
  let := D.finiteVariables
  let := coordinateOrder X i s g U hU D
  let : Fact (IsAffineOpen (i.left ⁻¹ᵁ U)) := ⟨hU.preimage i.left⟩
  let := AffineOpen.DeRhamTrace.polynomialSource R Y X f (i.left ⁻¹ᵁ U) D.coordinateIndex
  let := AffineOpen.DeRhamTrace.polynomialBaseTower R Y X f (i.left ⁻¹ᵁ U) D.coordinateIndex
  let := AffineOpen.DeRhamTrace.sourceEtale R Y X f (i.left ⁻¹ᵁ U) D.coordinateIndex
  exact Affine.EtaleCoordinateRestriction.etale R Y (homOfLE hVU) D.coordinateIndex
    ((hU.preimage i.left).preimage f.left) hV

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.ParameterOpenEtale
