import OAI.ArithmeticGeometry.Models.SpreadingOut.Separated
import OAI.ArithmeticGeometry.Models.SpreadingOut.ProperCover
import OAI.ArithmeticGeometry.Models.SpreadingOut.SmoothComponents

/-! # Cover Descent -/

namespace OAI.ArithmeticGeometry.Models.SpreadingOut.CoverDescent.Construction

noncomputable section

/-! Descend a covering morphism from a proper model and take its schematic
image to obtain a proper model of a smooth separated target. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.NumberField

universe u

theorem generic_map_surjective_of_compatible
    {S T : Scheme.{u}} (g : T ⟶ S)
    {X Y : Over T} {X₀ Y₀ : Over S}
    (pX : X.left ⟶ X₀.left) (pY : Y.left ⟶ Y₀.left)
    (hX : IsPullback pX X.hom X₀.hom g)
    (hY : IsPullback pY Y.hom Y₀.hom g)
    (f : X ⟶ Y) [Surjective f.left] (f₀ : X₀ ⟶ Y₀)
    (hf : pX ≫ f₀.left = f.left ≫ pY) :
    Surjective ((Over.pullback g).map f₀).left := by
  let B := Over.pullback g
  have h : hX.isoPullback.hom ≫ (B.map f₀).left = f.left ≫ hY.isoPullback.hom := by
    apply pullback.hom_ext
    · erw [Category.assoc, pullback.lift_fst, ← Category.assoc,
        hX.isoPullback_hom_fst, hf, Category.assoc, hY.isoPullback_hom_fst]
    · erw [Category.assoc, pullback.lift_snd, hX.isoPullback_hom_snd,
        Category.assoc, hY.isoPullback_hom_snd, f.w]
  have hs : Surjective (f.left ≫ hY.isoPullback.hom) := inferInstance
  rw [← h] at hs
  have := hs
  exact Surjective.of_comp hX.isoPullback.hom (B.map f₀).left

/-- A proper coefficient model of a scheme surjecting onto a smooth
separated scheme yields a proper coefficient model of the target. -/
theorem proper_model_of_cover
    {K : Type u} [Field K] [NumberField K]
    {Z X : Over (Spec (.of K))} [Smooth X.hom] [IsSeparated X.hom]
    (hX : Models.Scheme.Constructions.Foundations.FinitePresentationMorphism X.hom)
    (f : Z ⟶ X) [Surjective f.left]
    (P : Foundations.Constructions.CoefficientModel K Z) [IsProper P.model.hom] :
    ∃ M : Foundations.Constructions.CoefficientModel K X, IsProper M.model.hom := by
  classical
  obtain ⟨Q, hQ⟩ := Separated.Construction.separated_scheme_has_coefficient_model X hX
  have := hQ
  let s := P.coefficients ∪ Q.coefficients
  let P₁ := P.enlarge s Finset.subset_union_left
  let Q₁ := Q.enlarge s Finset.subset_union_right
  have : IsProper P₁.model.hom := inferInstanceAs (IsProper (pullback.snd P.model.hom
    (CoefficientSystem.Constructions.Foundations.coefficientBaseMap (𝓞 K) K Finset.subset_union_left)))
  have : IsSeparated Q₁.model.hom := inferInstanceAs (IsSeparated (pullback.snd Q.model.hom
    (CoefficientSystem.Constructions.Foundations.coefficientBaseMap (𝓞 K) K Finset.subset_union_right)))
  obtain ⟨t, hst, b, hb⟩ := ModelMorphisms.Constructions.Foundations.morphism_between_models_descends P₁.model Q₁.model
    P₁.finitePresentation Q₁.finitePresentation P₁.specialization Q₁.specialization
    P₁.cartesian Q₁.cartesian f
  let B := Over.pullback (CoefficientSystem.Constructions.Foundations.coefficientBaseMap (𝓞 K) K hst)
  let P₂ := B.obj P₁.model
  let Q₂ := B.obj Q₁.model
  let g := CoefficientSystem.Constructions.Foundations.genericBaseMap (𝓞 K) K t
  have hp := ModelMorphisms.Constructions.Foundations.genericModelLift_cartesian P₁.model P₁.specialization P₁.cartesian hst
  have hq := ModelMorphisms.Constructions.Foundations.genericModelLift_cartesian Q₁.model Q₁.specialization Q₁.cartesian hst
  have : IsProper P₂.hom := inferInstanceAs (IsProper
    (pullback.snd P₁.model.hom (CoefficientSystem.Constructions.Foundations.coefficientBaseMap (𝓞 K) K hst)))
  have : IsSeparated Q₂.hom := inferInstanceAs (IsSeparated
    (pullback.snd Q₁.model.hom (CoefficientSystem.Constructions.Foundations.coefficientBaseMap (𝓞 K) K hst)))
  have : LocallyOfFinitePresentation Q₁.model.hom := Q₁.finitePresentation.1
  have : LocallyOfFiniteType Q₂.hom := inferInstanceAs (LocallyOfFiniteType
    (pullback.snd Q₁.model.hom (CoefficientSystem.Constructions.Foundations.coefficientBaseMap (𝓞 K) K hst)))
  have : Surjective ((Over.pullback g).map b).left :=
    generic_map_surjective_of_compatible g _ _ hp hq f b hb
  have hsm : Smooth (hq.isoPullback.inv ≫ X.hom) := inferInstance
  rw [hq.isoPullback_inv_snd] at hsm
  have : Smooth (pullback.snd Q₂.hom g) := hsm
  have : IsReduced ((Over.pullback g).obj Q₂).left :=
    SmoothComponents.Construction.smooth_scheme_reduced (pullback.snd Q₂.hom g)
  obtain ⟨M, hM, ⟨e⟩⟩ := ProperCover.Construction.proper_cover_gives_proper_model g P₂ Q₂ b
  have := hM
  have := ModelFiniteness.Constructions.Foundations.coefficientBase_locallyNoetherian K t
  refine ⟨{
    coefficients := t
    model := M
    finitePresentation := ⟨inferInstance, inferInstance, inferInstance⟩
    genericIso := e ≪≫ Over.isoMk hq.isoPullback.symm hq.isoPullback_inv_snd
  }, hM⟩

end

end OAI.ArithmeticGeometry.Models.SpreadingOut.CoverDescent.Construction
