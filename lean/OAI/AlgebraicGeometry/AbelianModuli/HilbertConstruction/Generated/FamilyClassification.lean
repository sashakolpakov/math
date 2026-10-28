import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Generated.FlatUniversalFamily

/-! # Family Classification -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Generated.FamilyClassification

noncomputable section

/-! The affine classification equivalence pulls back the actual universal family to the generated family of the classified data. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {S : Scheme.{u}} {n B N : ℕ} {r : ℕ → ℕ} {R : CommRingCat.{u}}

theorem truncatedAffineUniversalData_over {f : Spec R ⟶ S}
    (x : Over.mk f ⟶ Truncated.GradedParameters.truncatedGradedParameters.{u, 0} (Fin (n + 1)) B r S) :
    Truncated.AffineUniversalData.truncatedAffineUniversalData x.left = Truncated.GradedRepresentation.truncatedGradedPointData x := by
  rcases x with ⟨x, y, hx⟩
  change Spec R ⟶ (Truncated.GradedParameters.truncatedGradedParameters (Fin (n + 1)) B r S).left at x
  dsimp only [Over.mk, CostructuredArrow.mk] at y
  have hx' : x ≫ (Truncated.GradedParameters.truncatedGradedParameters (Fin (n + 1)) B r S).hom = f := by
    simpa using hx
  subst f
  rfl

variable (f : Spec R ⟶ S)
variable (D : {D : Truncated.GradedClassification.TruncatedGradedQuotientData R (Fin (n + 1)) B r // D.GeneratedFromDegree N})

theorem truncatedGeneratedClassifier_data :
    Truncated.AffineUniversalData.truncatedAffineUniversalData
      ((Truncated.GeneratedParameters.truncatedGeneratedAffinePointEquiv R f D).left ≫ (Truncated.GeneratedParameters.truncatedGeneratedInclusion S n B r N).left) =
        D.val := by
  have hx := congrArg Over.Hom.left (Truncated.GeneratedParameters.truncatedGeneratedAffinePointEquiv_inclusion R f D)
  change (Truncated.GeneratedParameters.truncatedGeneratedAffinePointEquiv R f D).left ≫ (Truncated.GeneratedParameters.truncatedGeneratedInclusion S n B r N).left =
    (D.val.classifyingMap f).left at hx
  rw [hx, truncatedAffineUniversalData_over, Truncated.GeneratedParameters.truncatedGradedPointData_of_classifyingMap]

def truncatedGeneratedClassifier_familyIso : D.val.projectiveFamily ≅
    (Over.pullback (Truncated.GeneratedParameters.truncatedGeneratedAffinePointEquiv R f D).left).obj
      (Truncated.GeneratedFamily.truncatedGeneratedFamily S n B r N) :=
  eqToIso (congrArg Truncated.GradedClassification.TruncatedGradedQuotientData.projectiveFamily
    (truncatedGeneratedClassifier_data f D).symm) ≪≫
      Truncated.GeneratedFamily.truncatedGeneratedFamilyAffineIso (Truncated.GeneratedParameters.truncatedGeneratedAffinePointEquiv R f D).left

def generatedFlatClassifier_familyIso (hB : Truncated.FinitePersistence.truncatedFlatnessBound n N ≤ B) :
    D.val.projectiveFamily ≅ (Over.pullback (Truncated.GeneratedParameters.truncatedGeneratedAffinePointEquiv R f D).left).obj
      (FlatUniversalFamily.generatedFlatUniversalFamily S n B r N hB).scheme :=
  truncatedGeneratedClassifier_familyIso f D ≪≫
    (Over.pullback (Truncated.GeneratedParameters.truncatedGeneratedAffinePointEquiv R f D).left).mapIso
      (FlatUniversalFamily.generatedFlatUniversalFamilyIso S n B r N hB)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Generated.FamilyClassification
