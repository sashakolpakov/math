import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Configuration.FamilyTransport

/-! # Family Cocycle -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Configuration.FamilyCocycle

noncomputable section

/-! The uniquely restricted projective transports satisfy the
cocycle and identity laws as actual projective-family isomorphisms. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u v
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {R : Type u} [CommRing R] [IsNoetherianRing R] {n : ℕ} {P : Polynomial ℚ} {ι : Type v}

theorem configurationHilbertFamilyTransport_cocycle
    (I J K : SaturatedFlatIdeals.SaturatedFlatHilbertIdeal R n P) (v w z : ι → Fin (n + 1) → R)
    (D : ℕ) (hD : HilbertScheme.Presentations.Uniform.FamilyCoordinates.GradedHilbert.uniformHilbertFamilyDegree.{u} n P ≤ D)
    (hI : (Homogeneous.ConfigurationEvaluation.homogeneousConfigurationEvaluation v D).ker = HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.degreeRelations I.ideal.toIdeal D)
    (hJ : (Homogeneous.ConfigurationEvaluation.homogeneousConfigurationEvaluation w D).ker = HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.degreeRelations J.ideal.toIdeal D)
    (hK : (Homogeneous.ConfigurationEvaluation.homogeneousConfigurationEvaluation z D).ker = HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.degreeRelations K.ideal.toIdeal D)
    (hvw : ProjectiveTransport.ConfigurationFrameRelated v w) (hwz : ProjectiveTransport.ConfigurationFrameRelated w z) (hvz : ProjectiveTransport.ConfigurationFrameRelated v z)
    (σv σw : Fin (n + 1) → ι) (bv bw : ι)
    (hv : IsUnit (ProjectiveFrame.Discriminant.projectiveFrameDiscriminant (Pi.basisFun R (Fin (n + 1))) (fun k => v (σv k)) (v bv)))
    (hw : IsUnit (ProjectiveFrame.Discriminant.projectiveFrameDiscriminant (Pi.basisFun R (Fin (n + 1))) (fun k => w (σw k)) (w bw))) :
    FamilyTransport.configurationHilbertFamilyTransport I J v w D hD hI hJ hvw ≪≫
        FamilyTransport.configurationHilbertFamilyTransport J K w z D hD hJ hK hwz =
      FamilyTransport.configurationHilbertFamilyTransport I K v z D hD hI hK hvz := by
  apply Iso.ext
  apply Over.OverMorphism.ext
  apply (cancel_mono (HilbertScheme.Presentations.Projective.Quotient.GradedHilbert.projectiveQuotientInclusion K.ideal)).mp
  change ((FamilyTransport.configurationHilbertFamilyTransport I J v w D hD hI hJ hvw).hom.left ≫
    (FamilyTransport.configurationHilbertFamilyTransport J K w z D hD hJ hK hwz).hom.left) ≫ _ = _
  rw [Category.assoc, FamilyTransport.configurationHilbertFamilyTransport_ambient J K w z D hD hJ hK hwz,
    ← Category.assoc, FamilyTransport.configurationHilbertFamilyTransport_ambient I J v w D hD hI hJ hvw,
    Category.assoc, FamilyTransport.configurationHilbertFamilyTransport_ambient I K v z D hD hI hK hvz]
  exact congrArg (fun f => HilbertScheme.Presentations.Projective.Quotient.GradedHilbert.projectiveQuotientInclusion I.ideal ≫ f)
    (congrArg Over.Hom.left (ProjectiveTransport.configurationProjectiveTransport_cocycle v w z hvw hwz hvz σv σw bv bw hv hw))

theorem configurationHilbertFamilyTransport_self
    (I : SaturatedFlatIdeals.SaturatedFlatHilbertIdeal R n P) (v : ι → Fin (n + 1) → R)
    (D : ℕ) (hD : HilbertScheme.Presentations.Uniform.FamilyCoordinates.GradedHilbert.uniformHilbertFamilyDegree.{u} n P ≤ D)
    (hI : (Homogeneous.ConfigurationEvaluation.homogeneousConfigurationEvaluation v D).ker = HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.degreeRelations I.ideal.toIdeal D)
    (h : ProjectiveTransport.ConfigurationFrameRelated v v) (σ : Fin (n + 1) → ι) (b : ι)
    (hv : IsUnit (ProjectiveFrame.Discriminant.projectiveFrameDiscriminant (Pi.basisFun R (Fin (n + 1))) (fun k => v (σ k)) (v b))) :
    FamilyTransport.configurationHilbertFamilyTransport I I v v D hD hI hI h = Iso.refl _ := by
  apply Iso.ext
  apply Over.OverMorphism.ext
  apply (cancel_mono (HilbertScheme.Presentations.Projective.Quotient.GradedHilbert.projectiveQuotientInclusion I.ideal)).mp
  rw [FamilyTransport.configurationHilbertFamilyTransport_ambient]
  have he := congrArg Over.Hom.left (ProjectiveTransport.configurationProjectiveTransport_self v h σ b hv)
  rw [he]
  change HilbertScheme.Presentations.Projective.Quotient.GradedHilbert.projectiveQuotientInclusion I.ideal ≫ 𝟙 _ = HilbertScheme.Presentations.Projective.Quotient.GradedHilbert.projectiveQuotientInclusion I.ideal
  exact Category.comp_id _

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Configuration.FamilyCocycle
