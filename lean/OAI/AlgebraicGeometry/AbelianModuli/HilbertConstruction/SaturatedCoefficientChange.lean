import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SaturatedFlatIdeals
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.SaturationBaseChange
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coefficient.QuotientTwistingFrames
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Uniform.NoetherianFieldPolynomial
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Saturation.CoefficientComposition

/-! # Saturated Coefficient Change -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Actual coefficient change of a saturated flat Hilbert ideal is
the saturation of the extended ideal. Its projective family is the
scheme base change, compatibly with the ambient embedding and O(1). -/
set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u
variable {R A : Type u} [CommRing R] [IsNoetherianRing R] [CommRing A]
variable {n : ℕ} {P : Polynomial ℚ}
variable (I : SaturatedFlatIdeals.SaturatedFlatHilbertIdeal R n P) (φ : R →+* A)

def SaturatedFlatIdeals.SaturatedFlatHilbertIdeal.coefficientChange : SaturatedFlatIdeals.SaturatedFlatHilbertIdeal A n P := by
  letI := φ.toAlgebra
  let J := HilbertScheme.Presentations.Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := A) I.ideal
  have : Flat (HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading J)) := by
    let e := Projective.EmbeddingBaseChange.homogeneousProjectiveBaseChangeIso (A := A) I.ideal
    have : Flat (Projective.EmbeddingBaseChange.homogeneousProjectiveFamily I.ideal).hom := I.flat
    have : Flat ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R A)))).obj
        (Projective.EmbeddingBaseChange.homogeneousProjectiveFamily I.ideal)).hom :=
      inferInstanceAs (Flat (CategoryTheory.Limits.pullback.snd (Projective.EmbeddingBaseChange.homogeneousProjectiveFamily I.ideal).hom
        (Spec.map (CommRingCat.ofHom (algebraMap R A)))))
    have h : Flat (e.hom.left ≫ ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R A)))).obj
        (Projective.EmbeddingBaseChange.homogeneousProjectiveFamily I.ideal)).hom) := inferInstance
    have h' : Flat (Projective.EmbeddingBaseChange.homogeneousProjectiveFamily J).hom := e.hom.w ▸ h
    exact h'
  refine {
    ideal := HilbertScheme.Presentations.Projective.Saturation.GradedHilbert.projectiveSaturation J
    saturated := HilbertScheme.Presentations.Projective.Saturation.GradedHilbert.projectiveSaturation_isSaturated J
    flat := Projective.SaturationBaseChange.projectiveSaturation_flat J
    hilbert := fun p => ?_ }
  let ψ : A →+* p.asIdeal.ResidueField := algebraMap A p.asIdeal.ResidueField
  let : Algebra R p.asIdeal.ResidueField := (ψ.comp φ).toAlgebra
  change HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial (HilbertScheme.Presentations.Projective.Saturation.GradedHilbert.projectiveSaturation
    ((HilbertScheme.Presentations.Projective.Saturation.GradedHilbert.projectiveSaturation (I.ideal.map (HilbertScheme.Presentations.Graded.BaseChange.GradedHilbert.gradedCoefficientMap φ))).map (HilbertScheme.Presentations.Graded.BaseChange.GradedHilbert.gradedCoefficientMap ψ))).toIdeal P
  rw [HilbertScheme.Presentations.Saturation.CoefficientComposition.GradedHilbert.projectiveSaturation_coefficient_comp]
  exact HilbertScheme.Presentations.Uniform.NoetherianFieldPolynomial.GradedHilbert.uniformFamily_field_hasHilbertPolynomial I.ideal I.saturated P I.hilbert p.asIdeal.ResidueField

def SaturatedFlatIdeals.SaturatedFlatHilbertIdeal.coefficientChangeIso : Projective.EmbeddingBaseChange.homogeneousProjectiveFamily (I.coefficientChange φ).ideal ≅
    (Over.pullback (Spec.map (CommRingCat.ofHom φ))).obj (Projective.EmbeddingBaseChange.homogeneousProjectiveFamily I.ideal) := by
  letI := φ.toAlgebra
  exact Projective.SaturationBaseChange.homogeneousProjectiveSaturationIso (HilbertScheme.Presentations.Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := A) I.ideal) ≪≫
    Projective.EmbeddingBaseChange.homogeneousProjectiveBaseChangeIso (A := A) I.ideal

def SaturatedFlatIdeals.SaturatedFlatHilbertIdeal.coefficientChangeMorphism : Proj (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading (I.coefficientChange φ).ideal) ⟶
    Proj (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I.ideal) :=
  (I.coefficientChangeIso φ).hom.left ≫
    CategoryTheory.Limits.pullback.fst (Projective.EmbeddingBaseChange.homogeneousProjectiveFamily I.ideal).hom
      (Spec.map (CommRingCat.ofHom φ))

theorem SaturatedFlatIdeals.SaturatedFlatHilbertIdeal.coefficientChangeMorphism_ambient :
    I.coefficientChangeMorphism φ ≫ HilbertScheme.Presentations.Projective.Quotient.GradedHilbert.projectiveQuotientInclusion I.ideal =
      HilbertScheme.Presentations.Projective.Quotient.GradedHilbert.projectiveQuotientInclusion (I.coefficientChange φ).ideal ≫
        Projective.CoefficientFunctoriality.polynomialProjectiveMap (CommRingCat.ofHom φ) n := by
  let := φ.toAlgebra
  let J := HilbertScheme.Presentations.Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := A) I.ideal
  have hs : (Projective.SaturationBaseChange.homogeneousProjectiveSaturationIso J).hom.left ≫ HilbertScheme.Presentations.Projective.Quotient.GradedHilbert.projectiveQuotientInclusion J =
      HilbertScheme.Presentations.Projective.Quotient.GradedHilbert.projectiveQuotientInclusion (HilbertScheme.Presentations.Projective.Saturation.GradedHilbert.projectiveSaturation J) :=
    congrArg Over.Hom.left (Closed.EmbeddingKernelIso.closedEmbeddingKernelIso_embedding
      (Projective.EmbeddingBaseChange.homogeneousProjectiveEmbedding (HilbertScheme.Presentations.Projective.Saturation.GradedHilbert.projectiveSaturation J)) (Projective.EmbeddingBaseChange.homogeneousProjectiveEmbedding J)
      (HilbertScheme.Presentations.Projective.Saturation.GradedHilbert.projectiveSaturation_idealSheaf J))
  let a := (Projective.SaturationBaseChange.homogeneousProjectiveSaturationIso J).hom.left
  let e := Projective.EmbeddingBaseChange.homogeneousProjectiveBaseChangeIso (A := A) I.ideal
  let b := Spec.map (CommRingCat.ofHom (algebraMap R A))
  have he : e.hom.left ≫ CategoryTheory.Limits.pullback.fst
      (Projective.EmbeddingBaseChange.homogeneousProjectiveFamily I.ideal).hom b = HilbertScheme.Presentations.Projective.CoefficientMap.GradedHilbert.projectiveCoefficientMap (S := A) I.ideal :=
    (HilbertScheme.Presentations.Projective.BaseChange.GradedHilbert.projectiveQuotient_isPullback (S := A) I.ideal).isoPullback_hom_fst
  have hc : HilbertScheme.Presentations.Projective.CoefficientMap.GradedHilbert.projectiveCoefficientMap (S := A) I.ideal ≫ HilbertScheme.Presentations.Projective.Quotient.GradedHilbert.projectiveQuotientInclusion I.ideal =
      HilbertScheme.Presentations.Projective.Quotient.GradedHilbert.projectiveQuotientInclusion J ≫ Projective.CoefficientFunctoriality.polynomialProjectiveMap (CommRingCat.ofHom φ) n :=
    (HilbertConstruction.Polynomial.ProjectiveCoefficients.projectiveQuotientInclusion_coefficient (A := A) I.ideal).symm
  change ((a ≫ e.hom.left) ≫ CategoryTheory.Limits.pullback.fst
      (Projective.EmbeddingBaseChange.homogeneousProjectiveFamily I.ideal).hom b) ≫ HilbertScheme.Presentations.Projective.Quotient.GradedHilbert.projectiveQuotientInclusion I.ideal = _
  calc
    _ = a ≫ ((e.hom.left ≫ CategoryTheory.Limits.pullback.fst
        (Projective.EmbeddingBaseChange.homogeneousProjectiveFamily I.ideal).hom b) ≫ HilbertScheme.Presentations.Projective.Quotient.GradedHilbert.projectiveQuotientInclusion I.ideal) := by
      simp only [Category.assoc]
    _ = a ≫ (HilbertScheme.Presentations.Projective.CoefficientMap.GradedHilbert.projectiveCoefficientMap (S := A) I.ideal ≫ HilbertScheme.Presentations.Projective.Quotient.GradedHilbert.projectiveQuotientInclusion I.ideal) :=
      congrArg (fun k => a ≫ (k ≫ HilbertScheme.Presentations.Projective.Quotient.GradedHilbert.projectiveQuotientInclusion I.ideal)) he
    _ = a ≫ (HilbertScheme.Presentations.Projective.Quotient.GradedHilbert.projectiveQuotientInclusion J ≫ Projective.CoefficientFunctoriality.polynomialProjectiveMap (CommRingCat.ofHom φ) n) :=
      congrArg (fun k => a ≫ k) hc
    _ = (a ≫ HilbertScheme.Presentations.Projective.Quotient.GradedHilbert.projectiveQuotientInclusion J) ≫ Projective.CoefficientFunctoriality.polynomialProjectiveMap (CommRingCat.ofHom φ) n :=
      (Category.assoc _ _ _).symm
    _ = _ := congrArg (fun k => k ≫ Projective.CoefficientFunctoriality.polynomialProjectiveMap (CommRingCat.ofHom φ) n) hs

def SaturatedFlatIdeals.SaturatedFlatHilbertIdeal.coefficientChangeTwistingIso :
    ((ProjectiveTwisting.Bundle.projectiveTwistingBundle I.ideal 1).pullback (I.coefficientChangeMorphism φ)).sheaf ≅
      (ProjectiveTwisting.Bundle.projectiveTwistingBundle (I.coefficientChange φ).ideal 1).sheaf :=
  Coefficient.QuotientTwistingFrames.coefficientQuotientTwistingBundleIso (CommRingCat.ofHom φ) (I.coefficientChange φ).ideal I.ideal
    (I.coefficientChangeMorphism φ) (I.coefficientChangeMorphism_ambient φ)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
