import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Projective.CoefficientModels
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Proper.CoefficientReplacement
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Coefficient.SmoothModels
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Coefficient.GeneralModels
import OAI.ArithmeticGeometry.Models.SpreadingOut.Diagram

/-! # Smooth Projective Parameters -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.SmoothProjectiveParameters.Coefficients

noncomputable section

/-! Construct smooth proper finite coefficient models of projective
ambient-field schemes, retaining a closed embedding in standard projective
space. No arithmetic or coefficient-model existence is an input. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

theorem proper_model_pullback {S T : Scheme} (u : T ⟶ S) (M : Over S)
    (hM : IsProper M.hom) : IsProper ((Over.pullback u).obj M).hom := by
  let := hM
  exact inferInstanceAs (IsProper (pullback.snd M.hom u))

variable (R K : Type) [CommRing R] [Field K] [Algebra R K]

structure EmbeddedCoefficientModel (X : Over (Spec (.of K))) (n : ℕ) where
  toModel : Coefficient.Models.Coefficients.CoefficientModel R K X
  embedding : toModel.model ⟶ AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.affineProjectiveSpace (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientRing R K toModel.coefficients) n
  closedImmersion : IsClosedImmersion embedding.left

variable [IsNoetherianRing R]

/-- A given smooth projective scheme has an actual smooth proper
coefficient model with a closed standard projective embedding. -/
theorem smooth_projective_coefficient_model
    (X : Over (Spec (.of K))) [Smooth X.hom] (n : ℕ)
    (i : X ⟶ AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.affineProjectiveSpace K n) [IsClosedImmersion i.left] :
    ∃ D : EmbeddedCoefficientModel R K X n,
      Smooth D.toModel.model.hom ∧ IsProper D.toModel.model.hom := by
  have : IsProper X.hom := by rw [← i.w]; infer_instance
  obtain ⟨MX⟩ := Coefficient.GeneralModels.Coefficients.scheme_has_coefficient_model (R₀ := R) X
    ⟨inferInstance, inferInstance, inferInstance⟩
  let s := MX.coefficients
  let MP := Projective.CoefficientModels.Coefficients.projectiveCoefficientModel R K n s
  obtain ⟨t, hst, f, hf⟩ := Coefficient.Morphisms.Coefficients.morphism_between_models_descends MX.model MP.model
    MX.finitePresentation MP.finitePresentation MX.specialization MP.specialization
    MX.cartesian MP.cartesian i
  let F := Over.pullback (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBaseMap R K hst)
  let X₁ := F.obj MX.model
  let P₁ := F.obj MP.model
  let pX := Coefficient.Morphisms.Coefficients.genericModelLift MX.model MX.specialization MX.cartesian.w hst
  let pP := Coefficient.Morphisms.Coefficients.genericModelLift MP.model MP.specialization MP.cartesian.w hst
  have hX : IsPullback pX X.hom X₁.hom (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.genericBaseMap R K t) :=
    Coefficient.Morphisms.Coefficients.genericModelLift_cartesian MX.model MX.specialization MX.cartesian hst
  have hP : IsPullback pP (AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.affineProjectiveSpace K n).hom P₁.hom (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.genericBaseMap R K t) :=
    Coefficient.Morphisms.Coefficients.genericModelLift_cartesian MP.model MP.specialization MP.cartesian hst
  let eX : (Over.pullback (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.genericBaseMap R K t)).obj X₁ ≅ X :=
    Over.isoMk hX.isoPullback.symm hX.isoPullback_inv_snd
  let eP : (Over.pullback (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.genericBaseMap R K t)).obj P₁ ≅ AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.affineProjectiveSpace K n :=
    Over.isoMk hP.isoPullback.symm hP.isoPullback_inv_snd
  have he : (Over.pullback (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.genericBaseMap R K t)).map f ≫ eP.hom = eX.hom ≫ i :=
    ArithmeticGeometry.Models.SpreadingOut.Diagram.Construction.cartesian_generic_iso_compatibility _ pX pP hX hP i f hf
  have : IsIso eX.hom.left := ((Over.forget (Spec (.of K))).mapIso eX).isIso_hom
  have : IsIso eP.hom.left := ((Over.forget (Spec (.of K))).mapIso eP).isIso_hom
  have hc : IsClosedImmersion ((Over.pullback (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.genericBaseMap R K t)).map f).left := by
    apply (MorphismProperty.cancel_right_of_respectsIso @IsClosedImmersion _ eP.hom.left).mp
    rw [← Over.comp_left, he]
    exact inferInstanceAs (IsClosedImmersion (eX.hom.left ≫ i.left))
  have : IsProper P₁.hom := proper_model_pullback
    (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBaseMap R K hst) MP.model (Projective.CoefficientModels.Coefficients.projectiveCoefficientModel_proper R K n s)
  obtain ⟨N, j, hj, hproper, hfp, ⟨eN⟩⟩ := Proper.CoefficientReplacement.Coefficients.proper_coefficient_replacement X₁ P₁ f
  have : IsProper N.hom := hproper
  let D₀ : Coefficient.Models.Coefficients.CoefficientModel R K X := {
    coefficients := t
    model := N
    finitePresentation := hfp
    genericIso := eN ≪≫ eX }
  have : Smooth ((Over.pullback (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.genericBaseMap R K t)).obj N).hom := by
    have : IsIso D₀.genericIso.hom.left := ((Over.forget (Spec (.of K))).mapIso D₀.genericIso).isIso_hom
    rw [← D₀.genericIso.hom.w]
    infer_instance
  let φ := ((ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientDiagram R K).map (homOfLE hst)).hom
  let ePt : P₁ ≅ AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.affineProjectiveSpace (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientRing R K t) n :=
    (Projective.CoefficientModels.Coefficients.affineProjectiveBaseChangeIso φ n).symm
  have : IsIso ePt.hom.left := ((Over.forget (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBase R K t)).mapIso ePt).isIso_hom
  let j₀ : N ⟶ AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.affineProjectiveSpace (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientRing R K t) n := j ≫ ePt.hom
  have : IsClosedImmersion j.left := hj
  have hj₀ : IsClosedImmersion j₀.left := inferInstanceAs (IsClosedImmersion (j.left ≫ ePt.hom.left))
  obtain ⟨z, htz, hsm, hproperZ⟩ := Coefficient.SmoothModels.Coefficients.proper_model_eventually_smooth N
  let G := Over.pullback (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBaseMap R K htz)
  let ξ := ((ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientDiagram R K).map (homOfLE htz)).hom
  let ePz : G.obj (AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.affineProjectiveSpace (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientRing R K t) n) ≅
      AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.affineProjectiveSpace (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientRing R K z) n := (Projective.CoefficientModels.Coefficients.affineProjectiveBaseChangeIso ξ n).symm
  have : IsIso ePz.hom.left := ((Over.forget (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBase R K z)).mapIso ePz).isIso_hom
  have : IsClosedImmersion (G.map j₀).left := MorphismProperty.of_isPullback
    (ArithmeticGeometry.Models.FoundationsPullback.Constructions.pullback_over_map_isPullback (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBaseMap R K htz) j₀).flip hj₀
  let D : EmbeddedCoefficientModel R K X n := {
    toModel := D₀.enlarge z htz
    embedding := G.map j₀ ≫ ePz.hom
    closedImmersion := inferInstanceAs (IsClosedImmersion ((G.map j₀).left ≫ ePz.hom.left)) }
  exact ⟨D, hsm, hproperZ⟩

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.SmoothProjectiveParameters.Coefficients
