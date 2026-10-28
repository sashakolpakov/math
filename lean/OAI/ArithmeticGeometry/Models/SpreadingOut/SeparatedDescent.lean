import OAI.ArithmeticGeometry.Models.SpreadingOut.ClosedImmersionDescent
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts
import Mathlib.CategoryTheory.Limits.Constructions.Over.Products

/-! # Separated Descent -/

namespace OAI.ArithmeticGeometry.Models.SpreadingOut.SeparatedDescent.Construction

noncomputable section

/-! Separatedness descends by applying closed-immersion descent to the diagonal. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.NumberField

universe u

theorem over_diagonal_comp (S : Scheme.{u}) (X : Over S) :
    (Limits.diag X).left ≫ (Over.prodLeftIsoPullback X X).hom =
      pullback.diagonal X.hom := by
  apply pullback.hom_ext
  · rw [Category.assoc, Over.prodLeftIsoPullback_hom_fst, pullback.diagonal_fst]
    exact congrArg (fun f : X ⟶ X ↦ f.left) (prod.lift_fst (𝟙 X) (𝟙 X))
  · rw [Category.assoc, Over.prodLeftIsoPullback_hom_snd, pullback.diagonal_snd]
    exact congrArg (fun f : X ⟶ X ↦ f.left) (prod.lift_snd (𝟙 X) (𝟙 X))

theorem isSeparated_iff_over_diagonal {S : Scheme.{u}} (X : Over S) :
    IsSeparated X.hom ↔ IsClosedImmersion (Limits.diag X).left := by
  rw [← MorphismProperty.cancel_right_of_respectsIso @IsClosedImmersion _
    (Over.prodLeftIsoPullback X X).hom, over_diagonal_comp]
  exact isSeparated_iff _

theorem baseChange_diagonal_closed_iff
    {S T : Scheme.{u}} (g : T ⟶ S) (X : Over S) :
    IsClosedImmersion ((Over.pullback g).map (Limits.diag X)).left ↔
      IsSeparated ((Over.pullback g).obj X).hom := by
  let B := Over.pullback g
  have he : B.map (Limits.diag X) ≫ prodComparison B X X = Limits.diag (B.obj X) := by
    apply prod.hom_ext
    · rw [Category.assoc, prodComparison_fst, ← B.map_comp]
      simp only [Limits.diag, prod.lift_fst, B.map_id]
    · rw [Category.assoc, prodComparison_snd, ← B.map_comp]
      simp only [Limits.diag, prod.lift_snd, B.map_id]
  have : IsIso (prodComparison B X X).left :=
    inferInstanceAs (IsIso ((Over.forget T).map (prodComparison B X X)))
  rw [← MorphismProperty.cancel_right_of_respectsIso @IsClosedImmersion _
    (prodComparison B X X).left]
  change IsClosedImmersion (B.map (Limits.diag X) ≫ prodComparison B X X).left ↔ _
  rw [he]
  exact (isSeparated_iff_over_diagonal (B.obj X)).symm

theorem over_product_finitePresentation
    {S : Scheme.{u}} (X Y : Over S)
    (hX : Models.Scheme.Constructions.Foundations.FinitePresentationMorphism X.hom) (hY : Models.Scheme.Constructions.Foundations.FinitePresentationMorphism Y.hom) :
    Models.Scheme.Constructions.Foundations.FinitePresentationMorphism (X ⨯ Y).hom := by
  have : LocallyOfFinitePresentation X.hom := hX.1
  have : QuasiCompact X.hom := hX.2.1
  have : QuasiSeparated X.hom := hX.2.2
  have h := Over.isPullback_of_binaryFan_isLimit _ (prodIsProd X Y)
  have : LocallyOfFinitePresentation (prod.snd : X ⨯ Y ⟶ Y).left :=
    MorphismProperty.of_isPullback h hX.1
  have : QuasiCompact (prod.snd : X ⨯ Y ⟶ Y).left :=
    MorphismProperty.of_isPullback h hX.2.1
  have : QuasiSeparated (prod.snd : X ⨯ Y ⟶ Y).left :=
    MorphismProperty.of_isPullback h hX.2.2
  have : LocallyOfFinitePresentation Y.hom := hY.1
  have : QuasiCompact Y.hom := hY.2.1
  have : QuasiSeparated Y.hom := hY.2.2
  rw [← (prod.snd : X ⨯ Y ⟶ Y).w]
  exact ⟨inferInstance, inferInstance, inferInstance⟩

theorem closed_generic_map_eventually_closed
    {K : Type u} [Field K] [NumberField K] {s : Finset K}
    (X Y : Over (CoefficientSystem.Constructions.Foundations.coefficientBase (𝓞 K) K s))
    (hX : Models.Scheme.Constructions.Foundations.FinitePresentationMorphism X.hom) (hY : Models.Scheme.Constructions.Foundations.FinitePresentationMorphism Y.hom)
    (a : X ⟶ Y)
    [IsClosedImmersion ((Over.pullback (CoefficientSystem.Constructions.Foundations.genericBaseMap (𝓞 K) K s)).map a).left] :
    ∃ (t : Finset K) (h : s ⊆ t),
      IsClosedImmersion ((Over.pullback (CoefficientSystem.Constructions.Foundations.coefficientBaseMap (𝓞 K) K h)).map a).left := by
  let g := CoefficientSystem.Constructions.Foundations.genericBaseMap (𝓞 K) K s
  let B := Over.pullback g
  have hXg : IsPullback (pullback.fst X.hom g) (B.obj X).hom X.hom g :=
    IsPullback.of_hasPullback X.hom g
  have hYg : IsPullback (pullback.fst Y.hom g) (B.obj Y).hom Y.hom g :=
    IsPullback.of_hasPullback Y.hom g
  have hcompat : pullback.fst X.hom g ≫ a.left =
      (B.map a).left ≫ pullback.fst Y.hom g :=
    (FoundationsPullback.Constructions.pullback_over_map_isPullback g a).w.symm
  exact ClosedImmersionDescent.Construction.closed_immersion_eventually_on_models (X := B.obj X) (Y := B.obj Y) X Y hX hY
    (pullback.fst X.hom g) (pullback.fst Y.hom g)
    hXg hYg (B.map a) a hcompat

/-- A finite-presentation model with separated generic fiber is separated
after enlarging its finite set of coefficients. -/
theorem separated_generic_model_eventually_separated
    {K : Type u} [Field K] [NumberField K] {s : Finset K}
    (X : Over (CoefficientSystem.Constructions.Foundations.coefficientBase (𝓞 K) K s))
    (hX : Models.Scheme.Constructions.Foundations.FinitePresentationMorphism X.hom)
    [IsSeparated ((Over.pullback (CoefficientSystem.Constructions.Foundations.genericBaseMap (𝓞 K) K s)).obj X).hom] :
    ∃ (t : Finset K) (h : s ⊆ t),
      IsSeparated ((Over.pullback (CoefficientSystem.Constructions.Foundations.coefficientBaseMap (𝓞 K) K h)).obj X).hom := by
  have : IsClosedImmersion
      ((Over.pullback (CoefficientSystem.Constructions.Foundations.genericBaseMap (𝓞 K) K s)).map (Limits.diag X)).left :=
    (baseChange_diagonal_closed_iff _ X).mpr inferInstance
  obtain ⟨t, h, hc⟩ := closed_generic_map_eventually_closed X (X ⨯ X) hX
    (over_product_finitePresentation X X hX hX) (Limits.diag X)
  exact ⟨t, h, (baseChange_diagonal_closed_iff _ X).mp hc⟩

end

end OAI.ArithmeticGeometry.Models.SpreadingOut.SeparatedDescent.Construction
