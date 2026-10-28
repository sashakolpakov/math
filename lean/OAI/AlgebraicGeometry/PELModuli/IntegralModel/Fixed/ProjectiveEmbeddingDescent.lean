import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Coefficient.ProjectiveEmbedding
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Fixed.CoefficientModels
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Projective.CoefficientModels
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Coefficient.Morphisms
import OAI.ArithmeticGeometry.Models.SpreadingOut.Diagram

/-! # Projective Embedding Descent -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Fixed.ProjectiveEmbeddingDescent

noncomputable section

/-! Descend a complex projective embedding to finitely many coefficients,
keeping its source equal to the base change of the original scheme. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable (K L : Type) [CommRing K] [IsNoetherianRing K] [Field L] [Algebra K L]

theorem fixed_projective_embedding_generic_coefficient_model
    (X : Over (Spec (.of K))) (hX : ArithmeticGeometry.Models.Scheme.Constructions.Foundations.FinitePresentationMorphism X.hom)
    (n : ℕ)
    (i : (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap K L)))).obj X ⟶
      AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.affineProjectiveSpace L n) [IsClosedImmersion i.left] :
    ∃ (s : Finset L)
      (j : (Over.pullback (CoefficientModels.Coefficients.parameterBaseMap K L s)).obj X ⟶
        AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.affineProjectiveSpace (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientRing K L s) n),
      IsClosedImmersion ((Over.pullback (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.genericBaseMap K L s)).map j).left := by
  let MX := CoefficientModels.Coefficients.fixedSourceModel K L ∅ X hX
  let MP := Projective.CoefficientModels.Coefficients.projectiveCoefficientModel K L n ∅
  obtain ⟨t, h, f, hf⟩ := Coefficient.Morphisms.Coefficients.morphism_between_models_descends
    (R₀ := K) (K := L) (s := ∅)
    (X := (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap K L)))).obj X)
    (Y := AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.affineProjectiveSpace L n) MX.model MP.model
    MX.finitePresentation MP.finitePresentation MX.specialization MP.specialization
    MX.cartesian MP.cartesian i
  let F := Over.pullback (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBaseMap K L h)
  let X₁ := F.obj MX.model
  let P₁ := F.obj MP.model
  let pX := Coefficient.Morphisms.Coefficients.genericModelLift (R₀ := K) (K := L) (s := ∅)
    MX.model MX.specialization MX.cartesian.w h
  let pP := Coefficient.Morphisms.Coefficients.genericModelLift (R₀ := K) (K := L) (s := ∅)
    MP.model MP.specialization MP.cartesian.w h
  have hx : IsPullback pX
      ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap K L)))).obj X).hom
      X₁.hom (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.genericBaseMap K L t) :=
    Coefficient.Morphisms.Coefficients.genericModelLift_cartesian (R₀ := K) (K := L) (s := ∅)
      MX.model MX.specialization MX.cartesian h
  have hp : IsPullback pP (AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.affineProjectiveSpace L n).hom P₁.hom (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.genericBaseMap K L t) :=
    Coefficient.Morphisms.Coefficients.genericModelLift_cartesian (R₀ := K) (K := L) (s := ∅)
      MP.model MP.specialization MP.cartesian h
  let eX : (Over.pullback (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.genericBaseMap K L t)).obj X₁ ≅
      (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap K L)))).obj X :=
    Over.isoMk hx.isoPullback.symm hx.isoPullback_inv_snd
  let eP : (Over.pullback (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.genericBaseMap K L t)).obj P₁ ≅ AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.affineProjectiveSpace L n :=
    Over.isoMk hp.isoPullback.symm hp.isoPullback_inv_snd
  have he : (Over.pullback (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.genericBaseMap K L t)).map f ≫ eP.hom = eX.hom ≫ i :=
    ArithmeticGeometry.Models.SpreadingOut.Diagram.Construction.cartesian_generic_iso_compatibility _ pX pP hx hp i f hf
  have : IsIso eX.hom.left := ((Over.forget (Spec (.of L))).mapIso eX).isIso_hom
  have : IsIso eP.hom.left := ((Over.forget (Spec (.of L))).mapIso eP).isIso_hom
  have : IsClosedImmersion ((Over.pullback (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.genericBaseMap K L t)).map f).left := by
    apply (MorphismProperty.cancel_right_of_respectsIso @IsClosedImmersion _ eP.hom.left).mp
    rw [← Over.comp_left, he]
    exact inferInstanceAs (IsClosedImmersion (eX.hom.left ≫ i.left))
  let a : X₁ ≅ (Over.pullback (CoefficientModels.Coefficients.parameterBaseMap K L t)).obj X :=
    Group.BaseChangeComparisons.GroupBaseChange.iteratedIso X (CoefficientModels.Coefficients.parameterBaseMap K L ∅) (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBaseMap K L h)
      (CoefficientModels.Coefficients.parameterBaseMap K L t) (CoefficientModels.Coefficients.coefficient_parameterBaseMap K L h)
  let φ := ((ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientDiagram K L).map (homOfLE h)).hom
  let b : P₁ ≅ AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.affineProjectiveSpace (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientRing K L t) n :=
    (Projective.CoefficientModels.Coefficients.affineProjectiveBaseChangeIso φ n).symm
  let G := Over.pullback (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.genericBaseMap K L t)
  have : IsIso (G.map a.inv).left := ((Over.forget (Spec (.of L))).mapIso (G.mapIso a)).isIso_inv
  have : IsIso (G.map b.hom).left := ((Over.forget (Spec (.of L))).mapIso (G.mapIso b)).isIso_hom
  refine ⟨t, a.inv ≫ f ≫ b.hom, ?_⟩
  simp only [Functor.map_comp, Over.comp_left]
  exact inferInstanceAs (IsClosedImmersion ((G.map a.inv).left ≫ (G.map f).left ≫ (G.map b.hom).left))

theorem fixed_projective_embedding_coefficient_descent
    (X : Over (Spec (.of K))) (hX : ArithmeticGeometry.Models.Scheme.Constructions.Foundations.FinitePresentationMorphism X.hom)
    (n : ℕ)
    (i : (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap K L)))).obj X ⟶
      AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.affineProjectiveSpace L n) [IsClosedImmersion i.left] :
    ∃ (s : Finset L)
      (j : (Over.pullback (CoefficientModels.Coefficients.parameterBaseMap K L s)).obj X ⟶
        AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.affineProjectiveSpace (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientRing K L s) n),
      IsClosedImmersion j.left := by
  obtain ⟨s, f, hf⟩ := fixed_projective_embedding_generic_coefficient_model K L X hX n i
  have : IsClosedImmersion ((Over.pullback (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.genericBaseMap K L s)).map f).left := hf
  obtain ⟨t, h, j, hj⟩ := Coefficient.ProjectiveEmbedding.Coefficients.coefficient_projective_embedding_after_enlargement _ _
    (Coefficient.Finiteness.Coefficients.baseChange_finitePresentation _ X hX) f
  let a := Group.BaseChangeComparisons.GroupBaseChange.iteratedIso X (CoefficientModels.Coefficients.parameterBaseMap K L s) (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBaseMap K L h)
    (CoefficientModels.Coefficients.parameterBaseMap K L t) (CoefficientModels.Coefficients.coefficient_parameterBaseMap K L h)
  let φ := ((ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientDiagram K L).map (homOfLE h)).hom
  let b := (Projective.CoefficientModels.Coefficients.affineProjectiveBaseChangeIso φ n).symm
  have : IsClosedImmersion j.left := hj
  have : IsIso a.inv.left := ((Over.forget (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBase K L t)).mapIso a).isIso_inv
  have : IsIso b.hom.left := ((Over.forget (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBase K L t)).mapIso b).isIso_hom
  exact ⟨t, a.inv ≫ j ≫ b.hom,
    inferInstanceAs (IsClosedImmersion (a.inv.left ≫ j.left ≫ b.hom.left))⟩

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Fixed.ProjectiveEmbeddingDescent
