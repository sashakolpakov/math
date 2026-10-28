import OAI.AlgebraicGeometry.PELModuli.CMPoints.CoefficientFields
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Fixed.CoefficientModels
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Projective.CoefficientModels
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Coefficient.Morphisms
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.ClosedImmersionDescent
import OAI.ArithmeticGeometry.Models.SpreadingOut.Diagram

/-! # Fixed Projective Embedding Descent -/

namespace OAI.AlgebraicGeometry.PELModuli.CMPoints.FixedProjectiveEmbeddingDescent

noncomputable section

/-! Descend an embedding over an algebraic extension while keeping the
source equal to the base change of the specified original scheme. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.PELModuli.IntegralModel.ClosedImmersionDescent

variable (K L : Type) [Field K] [Field L] [Algebra K L] [Algebra.IsIntegral K L]

theorem fixed_projective_embedding_descends
    (X : Over (Spec (.of K))) (hX : ArithmeticGeometry.Models.Scheme.Constructions.Foundations.FinitePresentationMorphism X.hom)
    (n : ℕ)
    (i : (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap K L)))).obj X ⟶
      AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.affineProjectiveSpace L n) [IsClosedImmersion i.left] :
    ∃ (s : Finset L)
      (j : (Over.pullback (IntegralModel.Fixed.CoefficientModels.Coefficients.parameterBaseMap K L s)).obj X ⟶
        AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.affineProjectiveSpace (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientRing K L s) n),
      IsClosedImmersion j.left := by
  let MX := IntegralModel.Fixed.CoefficientModels.Coefficients.fixedSourceModel K L ∅ X hX
  let MP := IntegralModel.Projective.CoefficientModels.Coefficients.projectiveCoefficientModel K L n ∅
  obtain ⟨t, h, f, hf⟩ := IntegralModel.Coefficient.Morphisms.Coefficients.morphism_between_models_descends
    (R₀ := K) (K := L) (s := ∅)
    (X := (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap K L)))).obj X)
    (Y := AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.affineProjectiveSpace L n) MX.model MP.model
    MX.finitePresentation MP.finitePresentation MX.specialization MP.specialization
    MX.cartesian MP.cartesian i
  let F := Over.pullback (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBaseMap K L h)
  let X₁ := F.obj MX.model
  let P₁ := F.obj MP.model
  let pX := IntegralModel.Coefficient.Morphisms.Coefficients.genericModelLift (R₀ := K) (K := L) (s := ∅)
    MX.model MX.specialization MX.cartesian.w h
  let pP := IntegralModel.Coefficient.Morphisms.Coefficients.genericModelLift (R₀ := K) (K := L) (s := ∅)
    MP.model MP.specialization MP.cartesian.w h
  have hx : IsPullback pX
      ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap K L)))).obj X).hom
      X₁.hom (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.genericBaseMap K L t) :=
    IntegralModel.Coefficient.Morphisms.Coefficients.genericModelLift_cartesian (R₀ := K) (K := L) (s := ∅)
      MX.model MX.specialization MX.cartesian h
  have hp : IsPullback pP (AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.affineProjectiveSpace L n).hom P₁.hom (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.genericBaseMap K L t) :=
    IntegralModel.Coefficient.Morphisms.Coefficients.genericModelLift_cartesian (R₀ := K) (K := L) (s := ∅)
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
  let := CoefficientFields.algebraicCoefficientField K L t
  have : Flat (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.genericBaseMap K L t) := inferInstanceAs
    (Flat (Spec.map (CommRingCat.ofHom (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientRing K L t).val.toRingHom)))
  have : Surjective (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.genericBaseMap K L t) :=
    ⟨fun x => ⟨IsLocalRing.closedPoint L, Subsingleton.elim _ x⟩⟩
  have : QuasiCompact (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.genericBaseMap K L t) := inferInstanceAs
    (QuasiCompact (Spec.map (CommRingCat.ofHom (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientRing K L t).val.toRingHom)))
  have : IsClosedImmersion f.left := IntegralModel.ClosedImmersionDescent.closedImmersion_of_fpqc_baseChange (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.genericBaseMap K L t) f
  let a : X₁ ≅ (Over.pullback (IntegralModel.Fixed.CoefficientModels.Coefficients.parameterBaseMap K L t)).obj X :=
    IntegralModel.Group.BaseChangeComparisons.GroupBaseChange.iteratedIso X (IntegralModel.Fixed.CoefficientModels.Coefficients.parameterBaseMap K L ∅) (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBaseMap K L h)
      (IntegralModel.Fixed.CoefficientModels.Coefficients.parameterBaseMap K L t) (IntegralModel.Fixed.CoefficientModels.Coefficients.coefficient_parameterBaseMap K L h)
  let φ := ((ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientDiagram K L).map (homOfLE h)).hom
  let b : P₁ ≅ AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.affineProjectiveSpace (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientRing K L t) n :=
    (IntegralModel.Projective.CoefficientModels.Coefficients.affineProjectiveBaseChangeIso φ n).symm
  have : IsIso a.inv.left := ((Over.forget (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBase K L t)).mapIso a).isIso_inv
  have : IsIso b.hom.left := ((Over.forget (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBase K L t)).mapIso b).isIso_hom
  exact ⟨t, a.inv ≫ f ≫ b.hom,
    inferInstanceAs (IsClosedImmersion (a.inv.left ≫ f.left ≫ b.hom.left))⟩

end

end OAI.AlgebraicGeometry.PELModuli.CMPoints.FixedProjectiveEmbeddingDescent
