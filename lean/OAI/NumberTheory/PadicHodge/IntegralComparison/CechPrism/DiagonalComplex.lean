import OAI.NumberTheory.PadicHodge.IntegralComparison.CechPrism.DiagonalCone
import OAI.NumberTheory.PadicHodge.GeometricComparison.CechCone.TotalCoefficient
import OAI.NumberTheory.PadicHodge.IntegralComparison.CechPrism.EvaluationNaturality

/-! # Diagonal Complex -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.CechPrism.DiagonalComplex

noncomputable section

/-! The diagonal augmentation is a genuine cochain map into the
zeroth inner row, using the actual finite-product evaluation isomorphism. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite

universe u v w t
variable {C : Type u} [SemilatticeInf C]
  {A : Type v} [Category.{w} A] [Abelian A] [HasProducts.{t} A]
  {ι : Type t} [Finite ι] (U : ι → C)
  (Q : Cᵒᵖ ⥤ A) (B : Cᵒᵖ ⥤ Cᵒᵖ ⥤ A)
  (γ : (Functor.const Cᵒᵖ).obj Q ⟶ B)
  (h : ∀ I V : C, IsIso ((B.obj (op V)).map
    (homOfLE (inf_le_left : I ⊓ V ≤ I)).op))

open OAI.NumberTheory.PadicHodge.IntegralComparison.CechPrism.IntrinsicComponents.Intrinsic

def coordinates : (IntrinsicComponents.Intrinsic.complex U B).X 0 ≅
    (NonemptyCechNerve.complexFunctor U).obj
      ((B ⋙ NonemptyCechNerve.complexFunctor U) ⋙ HomologicalComplex.eval A (.up ℕ) 0) :=
  GeometricComparison.Finite.CechCoefficientChange.FiniteCechCoefficientChange.complexIso (HomologicalComplex.eval A (.up ℕ) 0)
    (NonemptyCechNerve.nerve U) (GeometricComparison.CechCone.TotalCoefficient.CechConeTotalCoefficient.finite_indices U)
    (B ⋙ NonemptyCechNerve.complexFunctor U)

def map : (NonemptyCechNerve.complexFunctor U).obj Q ⟶ (IntrinsicComponents.Intrinsic.complex U B).X 0 :=
  (NonemptyCechNerve.complexFunctor U).map
    (DiagonalCone.coefficient U Q B γ h) ≫ (coordinates U B).inv

theorem coordinates_projection (n : ℕ) (a : Fin 1 → ι) (b : Fin (n + 1) → ι) :
    (coordinates U B).hom.f n ≫
      NonemptyCechDifferential.projection U
        ((B ⋙ NonemptyCechNerve.complexFunctor U) ⋙ HomologicalComplex.eval A (.up ℕ) 0) n b ≫
      NonemptyCechDifferential.projection U (B.obj (op (∏ᶜ (U ∘ b)))) 0 a =
        IntrinsicComponents.Intrinsic.projection U B 0 n a b := by
  erw [GeometricComparison.Finite.CechCoefficientChange.FiniteCechCoefficientChange.hom_f]
  exact piComparison_comp_π_assoc (HomologicalComplex.eval A (.up ℕ) 0)
    (fun b : Fin (n + 1) → ι =>
      (NonemptyCechNerve.complexFunctor U).obj (B.obj (op (∏ᶜ (U ∘ b))))) b
    (NonemptyCechDifferential.projection U (B.obj (op (∏ᶜ (U ∘ b)))) 0 a)

theorem map_projection (n : ℕ) (a : Fin 1 → ι) (b : Fin (n + 1) → ι) :
    (DiagonalComplex.map U Q B γ h).f n ≫ IntrinsicComponents.Intrinsic.projection U B 0 n a b =
      NonemptyCechDifferential.projection U Q n b ≫
        (γ.app (op (∏ᶜ (U ∘ b)))).app (op (∏ᶜ (U ∘ b))) ≫
          (GeometricComparison.Semilattice.LocalCone.SemilatticeLocalCone.cone C (∏ᶜ (U ∘ b))
            (B.obj (op (∏ᶜ (U ∘ b)))) (fun I => h I (∏ᶜ (U ∘ b)))).app
              (op (∏ᶜ (U ∘ a))) := by
  rw [← coordinates_projection]
  dsimp only [DiagonalComplex.map, HomologicalComplex.comp_f]
  have hi : (coordinates U B).inv.f n ≫ (coordinates U B).hom.f n = 𝟙 _ :=
    congrArg (fun f => f.f n) (coordinates U B).inv_hom_id
  erw [Category.assoc, ← Category.assoc ((coordinates U B).inv.f n)
    ((coordinates U B).hom.f n), hi, Category.id_comp]
  change Limits.Pi.map (fun b : Fin (n + 1) → ι =>
    (DiagonalCone.coefficient U Q B γ h).app (op (∏ᶜ (U ∘ b)))) ≫ _ = _
  erw [Pi.map_π_assoc, DiagonalCone.coefficient_projection]
  rfl

theorem value_projection (n : ℕ) (a : Fin 1 → ι) (b : Fin (n + 1) → ι) :
    (DiagonalComplex.map U Q B γ h).f n ≫ IntrinsicComponents.Intrinsic.projection U B 0 n a b =
      EvaluationNaturality.value U Q B γ h
        (∏ᶜ (U ∘ a)) (∏ᶜ (U ∘ b)) n (List.ofFn b) := by
  rw [map_projection, SemilatticeCechAmalgamation.diagonal_factorization Q B γ h]
  dsimp only [EvaluationNaturality.value]
  rw [Cech.LocalTupleEvaluation.value_ofFn U Q _ b inf_le_right, Category.assoc]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.CechPrism.DiagonalComplex
