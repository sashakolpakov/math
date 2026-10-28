import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Stalk.ScalarMaps
import OAI.AlgebraicGeometry.Foundations.Scheme.ProjectiveChart
import OAI.AlgebraicGeometry.Foundations.Scheme.ClosedImmersionDimension

/-! # Coordinate Algebra -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projective.CoordinateAlgebra

noncomputable section

/-! The polynomial description of a projective coordinate chart is
an algebra isomorphism for the actual structure map to Spec C. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable (n : ℕ) (i : Fin (n + 1))

def ringEquiv : Foundations.Scheme.ProjectiveChartToPolynomial.projectiveChartPolynomial n i ≃+*
    Γ(Foundations.Scheme.ProjectiveSpace.projectiveSpace n, Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen n i) :=
  (Foundations.Scheme.PolynomialToProjectiveChart.projectiveChartRingEquiv n i).symm.trans
    (Proj.basicOpenIsoAway (Foundations.Scheme.ProjectiveSpace.projectiveGrading n) (MvPolynomial.X i)
      (Foundations.Scheme.ProjectiveChartToPolynomial.projectiveVariable_homogeneous n i) (by decide : 0 < 1)).commRingCatIsoToRingEquiv

theorem toSpec :
    (Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen_isAffine n i).isoSpec.hom ≫
      Spec.map (CommRingCat.ofHom (ringEquiv n i).toRingHom) =
        (Foundations.Scheme.ProjectiveChart.projectiveCoordinateIsoSpec n i).hom := by
  change (Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen n i).toSpecΓ ≫
    Spec.map (CommRingCat.ofHom (Foundations.Scheme.PolynomialToProjectiveChart.projectiveChartRingEquiv n i).symm.toRingHom ≫
      Proj.awayToSection (Foundations.Scheme.ProjectiveSpace.projectiveGrading n) (MvPolynomial.X i)) = _
  rw [Spec.map_comp, ← Category.assoc]
  rfl

theorem fromSpec :
    Spec.map (CommRingCat.ofHom (ringEquiv n i).toRingHom) ≫ Foundations.Scheme.ProjectiveChart.projectiveAffineChartMap n i =
      (Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen_isAffine n i).fromSpec := by
  apply (cancel_epi (Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen_isAffine n i).isoSpec.hom).mp
  rw [← Category.assoc, toSpec]
  simp [Foundations.Scheme.ProjectiveChart.projectiveAffineChartMap]

theorem constants :
    (ringEquiv n i).toRingHom.comp (MvPolynomial.C : ℂ →+* Foundations.Scheme.ProjectiveChartToPolynomial.projectiveChartPolynomial n i) =
      Foundations.Scheme.SpecScalarTransport.specSectionScalarMap (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n) (Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen n i) := by
  suffices h : CommRingCat.ofHom ((ringEquiv n i).toRingHom.comp MvPolynomial.C) =
      CommRingCat.ofHom (Foundations.Scheme.SpecScalarTransport.specSectionScalarMap (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n) (Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen n i)) by
    exact congrArg CommRingCat.Hom.hom h
  apply Spec.map_injective
  change Spec.map (CommRingCat.ofHom MvPolynomial.C ≫ CommRingCat.ofHom (ringEquiv n i).toRingHom) = _
  rw [Spec.map_comp]
  change Spec.map (CommRingCat.ofHom (ringEquiv n i).toRingHom) ≫ Foundations.Scheme.ProjectiveChart.projectiveChartPolynomialToBase n i = _
  rw [← Foundations.Scheme.ProjectiveChart.projectiveAffineChartMap_over, ← Category.assoc, CoordinateAlgebra.fromSpec,
    Foundations.Scheme.SpecScalarTransport.specSectionScalarMap_fromSpec _ _ (Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen_isAffine n i)]

def algebraEquiv :
    letI := Foundations.Scheme.SpecScalarTransport.specSectionScalarAlgebra (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n) (Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen n i)
    Foundations.Scheme.ProjectiveChartToPolynomial.projectiveChartPolynomial n i ≃ₐ[ℂ] Γ(Foundations.Scheme.ProjectiveSpace.projectiveSpace n, Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen n i) := by
  let := Foundations.Scheme.SpecScalarTransport.specSectionScalarAlgebra (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n) (Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen n i)
  exact { ringEquiv n i with commutes' := fun c => RingHom.congr_fun (constants n i) c }

def quotientMap {X : Scheme} (j : X ⟶ Foundations.Scheme.ProjectiveSpace.projectiveSpace n) :
    letI := Foundations.Scheme.SpecScalarTransport.specSectionScalarAlgebra (j ≫ Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n) (j ⁻¹ᵁ Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen n i)
    Foundations.Scheme.ProjectiveChartToPolynomial.projectiveChartPolynomial n i →ₐ[ℂ] Γ(X, j ⁻¹ᵁ Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen n i) := by
  let := Foundations.Scheme.SpecScalarTransport.specSectionScalarAlgebra (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n) (Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen n i)
  let := Foundations.Scheme.SpecScalarTransport.specSectionScalarAlgebra (j ≫ Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n) (j ⁻¹ᵁ Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen n i)
  exact (Foundations.Scheme.ClosedImmersionDimension.sectionPullbackAlgHom j (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n) (Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen n i)).comp
    (algebraEquiv n i).toAlgHom

theorem quotientMap_surjective {X : Scheme} (j : X ⟶ Foundations.Scheme.ProjectiveSpace.projectiveSpace n) [IsClosedImmersion j] :
    Function.Surjective (quotientMap n i j) := by
  let := Foundations.Scheme.SpecScalarTransport.specSectionScalarAlgebra (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n) (Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen n i)
  let := Foundations.Scheme.SpecScalarTransport.specSectionScalarAlgebra (j ≫ Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n) (j ⁻¹ᵁ Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen n i)
  exact (Foundations.Scheme.ClosedImmersionDimension.sectionPullbackAlgHom_surjective j (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n) (Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen n i)
    (Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen_isAffine n i)).comp (algebraEquiv n i).surjective

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projective.CoordinateAlgebra
