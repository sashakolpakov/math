import OAI.AlgebraicGeometry.PELModuli.IntegralModel.SmoothProjectiveParameters
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Coefficient.GroupModels

/-! # Embedded Group Parameters -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.EmbeddedGroupParameters.Coefficients

noncomputable section

/-! Construct embedded smooth proper commutative group families over finite
coefficient rings, with their actual group-compatible ambient-field fiber. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable (R K : Type) [CommRing R] [Field K] [Algebra R K] [IsNoetherianRing R]

/-- Both the projective model and its commutative group structure are
constructed from the given smooth projective ambient-field group. -/
theorem smooth_projective_group_coefficient_model
    (X : Over (Spec (.of K))) [GrpObj X] [IsCommMonObj X] [Smooth X.hom]
    (n : ℕ) (i : X ⟶ AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.affineProjectiveSpace K n) [IsClosedImmersion i.left] :
    ∃ (D : SmoothProjectiveParameters.Coefficients.EmbeddedCoefficientModel R K X n) (groupD : GrpObj D.toModel.model),
      Smooth D.toModel.model.hom ∧ IsProper D.toModel.model.hom ∧
      (letI := groupD; IsCommMonObj D.toModel.model) ∧
      (letI := groupD
       letI : GrpObj ((Over.pullback (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.genericBaseMap R K D.toModel.coefficients)).obj
         D.toModel.model) := Functor.grpObjObj
           (F := Over.pullback (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.genericBaseMap R K D.toModel.coefficients))
           (G := D.toModel.model)
       IsMonHom D.toModel.genericIso.hom) := by
  obtain ⟨D₀, hsm, hproper⟩ := SmoothProjectiveParameters.Coefficients.smooth_projective_coefficient_model R K X n i
  let M := D₀.toModel.model
  let s := D₀.toModel.coefficients
  let H := Over.pullback (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.genericBaseMap R K s)
  have : Smooth M.hom := hsm
  have : IsProper M.hom := hproper
  let genericGroup : GrpObj (H.obj M) := GrpObj.ofIso D₀.toModel.genericIso.symm
  have : IsCommMonObj (H.obj M) := ArithmeticGeometry.Models.SpreadingOut.GroupReflection.Construction.commutative_group_of_iso D₀.toModel.genericIso.symm
  obtain ⟨t, h, groupN, hcomm, hgroup⟩ := Coefficient.GroupModels.Coefficients.commutative_group_model_after_enlargement M
  let F := Over.pullback (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBaseMap R K h)
  let G := Over.pullback (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.genericBaseMap R K t)
  let N := F.obj M
  let := groupN
  let : GrpObj (G.obj N) := Functor.grpObjObj (F := G)
  let c : G.obj N ≅ H.obj M := (Coefficient.GenericMorphisms.Coefficients.coefficientGenericComparison (R₀ := R) h).app M
  have hc : IsMonHom c.hom := ArithmeticGeometry.Models.SpreadingOut.GroupReflection.Construction.image_group_iso_isMonHom G N (H.obj M) c groupN hgroup
  have he : IsMonHom D₀.toModel.genericIso.hom :=
    ArithmeticGeometry.Models.SpreadingOut.GroupReflection.Construction.transported_group_iso_isMonHom D₀.toModel.genericIso
  have hsN : Smooth N.hom := inferInstanceAs (Smooth (pullback.snd M.hom _))
  have hpN : IsProper N.hom := inferInstanceAs (IsProper (pullback.snd M.hom _))
  let DN : Coefficient.Models.Coefficients.CoefficientModel R K X := {
    coefficients := t
    model := N
    finitePresentation := ⟨inferInstance, inferInstance, inferInstance⟩
    genericIso := c ≪≫ D₀.toModel.genericIso }
  let φ := ((ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientDiagram R K).map (homOfLE h)).hom
  let eP : F.obj (AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.affineProjectiveSpace (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientRing R K s) n) ≅
      AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.affineProjectiveSpace (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientRing R K t) n :=
    (Projective.CoefficientModels.Coefficients.affineProjectiveBaseChangeIso φ n).symm
  have : IsIso eP.hom.left := ((Over.forget (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBase R K t)).mapIso eP).isIso_hom
  have : IsClosedImmersion (F.map D₀.embedding).left := MorphismProperty.of_isPullback
    (ArithmeticGeometry.Models.FoundationsPullback.Constructions.pullback_over_map_isPullback (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBaseMap R K h) D₀.embedding).flip D₀.closedImmersion
  let D : SmoothProjectiveParameters.Coefficients.EmbeddedCoefficientModel R K X n := {
    toModel := DN
    embedding := F.map D₀.embedding ≫ eP.hom
    closedImmersion := inferInstanceAs
      (IsClosedImmersion ((F.map D₀.embedding).left ≫ eP.hom.left)) }
  exact ⟨D, groupN, hsN, hpN, hcomm,
    inferInstanceAs (IsMonHom (c.hom ≫ D₀.toModel.genericIso.hom))⟩

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.EmbeddedGroupParameters.Coefficients
