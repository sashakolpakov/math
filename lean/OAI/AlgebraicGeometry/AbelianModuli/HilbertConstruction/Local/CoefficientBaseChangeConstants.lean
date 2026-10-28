import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Local.ProjectiveGlobalFunctions

/-! # Coefficient Base Change Constants -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Local.CoefficientBaseChangeConstants

noncomputable section

/-! The uniform matrix over a noetherian coefficient ring proves global-function constancy after extension to any local coefficient algebra, without noetherianity of that algebra. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

theorem localCoefficientBaseChange_globalFunctions_isIso
    {R A : Type u} [CommRing R] [IsNoetherianRing R] [CommRing A] [Algebra R A] [IsLocalRing A]
    {n : ℕ} (I : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n))
    [IsProper (HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I))]
    [Smooth (HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I))]
    [GeometricallyConnected (HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I))]
    (x : Spec (.of R) ⟶ Proj (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I))
    (hx : x ≫ HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I) = 𝟙 _) :
    IsIso (HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading (HilbertScheme.Presentations.Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := A) I))).appTop := by
  obtain ⟨m, k, B, hB⟩ := Projective.GlobalFunctionsMatrix.flatProjectiveCoordinate_globalFunctions_uniform_matrix I
  let K := IsLocalRing.ResidueField A
  have hd : Module.finrank K (Matrix.toLin' (B.map (algebraMap R K))).ker ≤ 1 :=
    (ProjectiveCoordinate.ConnectedFieldCriterion.projectiveCoordinate_connected_field_kernel I x hx B (Classical.choice (hB K))).mp inferInstance
  have hm : (B.map (algebraMap R A)).map (algebraMap A K) = B.map (algebraMap R K) := by
    ext i j
    exact (IsScalarTower.algebraMap_apply R A K (B i j)).symm
  have hd' : Module.finrank K (Matrix.toLin' ((B.map (algebraMap R A)).map (algebraMap A K))).ker ≤ 1 := by
    rw [hm]
    exact hd
  let p := HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I)
  let pA := HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading (HilbertScheme.Presentations.Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := A) I))
  let c := Spec.map (CommRingCat.ofHom (algebraMap R A))
  let H := HilbertScheme.Presentations.Projective.BaseChange.GradedHilbert.projectiveQuotient_isPullback (S := A) I
  let xA := PointedFamilyFiberConnectedness.schemeSectionBaseChange p x hx c ≫ H.isoPullback.inv
  have hxA : xA ≫ pA = 𝟙 _ :=
    (Category.assoc _ _ _).trans
      ((congrArg (fun f => PointedFamilyFiberConnectedness.schemeSectionBaseChange p x hx c ≫ f) H.isoPullback_inv_snd).trans
        (PointedFamilyFiberConnectedness.schemeSectionBaseChange_section p x hx c))
  let σ := Section.CoefficientRetraction.sectionCoefficientRetraction pA xA hxA
  have he := MatrixAlgebraModel.localMatrixModel_algebraMap_bijective (B.map (algebraMap R A))
    (Classical.choice (hB A)) σ.toLinearMap σ.map_one hd'
  change Function.Bijective (Coefficient.AlgebraPresheaf.coefficientSectionMap (Affine.ChartCoefficientSections.schemeGlobalCoefficient pA) ⊤) at he
  rw [Coefficient.GlobalFunctionDimension.coefficientSectionMap_top] at he
  exact (ConcreteCategory.isIso_iff_bijective pA.appTop).mpr ((Coefficient.GlobalFunctionDimension.schemeGlobalCoefficient_bijective_iff pA).mp he)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Local.CoefficientBaseChangeConstants
