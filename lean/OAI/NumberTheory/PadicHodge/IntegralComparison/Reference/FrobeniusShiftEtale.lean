import OAI.NumberTheory.PadicHodge.IntegralComparison.Geometric.FrobeniusFactorShiftEtale
import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.FiberwiseFlatness

/-! # Frobenius Shift Etale -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Reference.FrobeniusShiftEtale

noncomputable section

/-! Prime-to-characteristic positive shifts of Frobenius are finite,
surjective and étale on the original finite-field group scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.Obj

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

theorem groupHom_flat {S : Scheme.{u}} {X Y : Over S} [GrpObj X] [GrpObj Y]
    [Smooth X.hom] [Smooth Y.hom] (f : X ⟶ Y) [IsMonHom f]
    [IsFinite f.left] [Surjective f.left] : Flat f.left := by
  let : LocallyOfFinitePresentation (f.left ≫ Y.hom) := by rw [Over.w]; infer_instance
  let : LocallyOfFinitePresentation f.left := AlgebraicGeometry.AbelianScheme.TorsionQuotient.FinitePresentationOf.FinitePresentation.of_comp f.left Y.hom
  apply ArithmeticGeometry.OrdinaryLocus.Openness.FiberwiseFlatness.Construction.flat_finite_of_flat_geometric_baseChanges f
  intro K _ _ t
  let F := Over.pullback t
  let : Smooth (F.obj X).hom :=
    inferInstanceAs (Smooth (CategoryTheory.Limits.pullback.snd X.hom t))
  let : Smooth (F.obj Y).hom :=
    inferInstanceAs (Smooth (CategoryTheory.Limits.pullback.snd Y.hom t))
  let : IsFinite (F.map f).left := MorphismProperty.overPullbackMap (P := @IsFinite) t f inferInstance
  let : Surjective (F.map f).left := MorphismProperty.overPullbackMap (P := @Surjective) t f inferInstance
  exact AlgebraicGeometry.FormalGeometry.Completion.Finite.GroupHomFlat.Construction.finite_surjective_groupHom_flat (F.map f)

variable (k : Type u) [Field k] [Fintype k]
  (X : Over (Spec (CommRingCat.of k))) [GrpObj X] [IsCommMonObj X]

theorem formallyUnramified (n : ℕ) (hn : (n : k) ≠ 0) :
    FormallyUnramified ((n : AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd X) + AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.algebraicFrobenius k X).toMul.hom.hom.left := by
  simpa only [neg_one_mul, sub_neg_eq_add] using
    Frobenius.FactorShiftUnramified.formallyUnramified k X (-1) n hn

variable [IsProper X.hom] [Smooth X.hom] [GeometricallyIntegral X.hom]

theorem finite_etale (n : ℕ) (hn : (n : k) ≠ 0) :
    IsFinite ((n : AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd X) + AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.algebraicFrobenius k X).toMul.hom.hom.left ∧
    Surjective ((n : AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd X) + AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.algebraicFrobenius k X).toMul.hom.hom.left ∧
    Etale ((n : AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd X) + AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.algebraicFrobenius k X).toMul.hom.hom.left := by
  let f := ((n : AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd X) + AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.algebraicFrobenius k X).toMul.hom.hom
  let : FormallyUnramified f.left := formallyUnramified k X n hn
  let : IsProper (f.left ≫ X.hom) := by rw [Over.w]; infer_instance
  let : IsProper f.left := IsProper.of_comp f.left X.hom
  let : IsFinite f.left := AlgebraicGeometry.AbelianScheme.TorsionQuotient.Quasi.TorsionGeometry.finite_of_proper_formallyUnramified f.left
  let : IsIntegral X.left := GeometricallyIntegral.isIntegral_of_subsingleton X.hom
  let : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  let : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  let : IsNoetherian X.left := ⟨⟩
  let : Surjective f.left := ArithmeticGeometry.OrdinaryLocus.Openness.FiniteEndomorphism.Construction.surjective_finite_endomorphism_of_isIntegral f.left
  let : Flat f.left := groupHom_flat f
  let : LocallyOfFinitePresentation (f.left ≫ X.hom) := by rw [Over.w]; infer_instance
  let : LocallyOfFinitePresentation f.left := AlgebraicGeometry.AbelianScheme.TorsionQuotient.FinitePresentationOf.FinitePresentation.of_comp f.left X.hom
  exact ⟨inferInstance, inferInstance, Etale.of_formallyUnramified_of_flat f.left⟩

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Reference.FrobeniusShiftEtale
