import OAI.NumberTheory.PadicHodge.IntegralComparison.DoubleCechRegrouping
import OAI.NumberTheory.PadicHodge.IntegralComparison.TripleTotal.HorizontalEdge

/-! # Double Cech Global Augmentation -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.DoubleCechGlobalAugmentation

noncomputable section

/-! Canonical triple regrouping carries the genuine global cone
augmentation to the outer augmentation of its row totals. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite

universe u v w z
variable {C : Type u} [Category.{v} C] [HasBinaryProducts C]
  {A : Type w} [Category.{z} A] [Abelian A] [HasProducts.{0} A] [HasCoproducts.{0} A]
  {ι : Type} [Finite ι] (U : ι → C)
  (P : Cᵒᵖ ⥤ HomologicalComplex₂ A (.up ℕ) (.up ℕ))
  (M : HomologicalComplex₂ A (.up ℕ) (.up ℕ))
  (η : (Functor.const Cᵒᵖ).obj M ⟶ P)
attribute [local instance] TripleTotal.Rotation.total TripleTotal.Rotation.complexTotal

local notation "F" => OAI.NumberTheory.PadicHodge.IntegralComparison.TripleTotal.RowCoordinates.rowFunctor (A := A)
local notation "S" => OAI.NumberTheory.PadicHodge.IntegralComparison.DoubleCechRegrouping.triple U P
local notation "a" => OAI.NumberTheory.PadicHodge.GeometricComparison.CechCone.Total.CechConeTotal.zeroMap U P M η
local notation "wa" => OAI.NumberTheory.PadicHodge.GeometricComparison.CechCone.Total.CechConeTotal.cocycle U P M η

def cone : (Functor.const Cᵒᵖ).obj ((F).obj M) ⟶ P ⋙ F :=
  (Functor.constComp Cᵒᵖ M F).inv ≫ Functor.whiskerRight η F

def map := GeometricComparison.CechCone.Total.CechConeTotal.augmentation U (P ⋙ F) ((F).obj M) (cone P M η)

def coefficientIso := GeometricComparison.Finite.CechCoefficientChange.FiniteCechCoefficientChange.complexIso F
  (NonemptyCechNerve.nerve U) (fun _ => inferInstanceAs (Finite (Fin _ → ι))) P

theorem zeroMap : (F).map a ≫ (coefficientIso U P).hom.f 0 =
    GeometricComparison.CechCone.Total.CechConeTotal.zeroMap U (P ⋙ F) ((F).obj M) (cone P M η) := by
  dsimp only [coefficientIso]
  erw [GeometricComparison.Finite.CechCoefficientChange.FiniteCechCoefficientChange.hom_f]
  apply Pi.hom_ext
  intro (b : Fin 1 → ι)
  erw [Category.assoc, piComparison_comp_π, ← Functor.map_comp]
  change (F).map (Pi.lift (fun b : Fin 1 → ι => η.app (op (∏ᶜ (U ∘ b)))) ≫ Pi.π _ b) =
    Pi.lift (fun b : Fin 1 → ι => (cone P M η).app (op (∏ᶜ (U ∘ b)))) ≫ Pi.π _ b
  erw [Pi.lift_comp_π, Pi.lift_comp_π]
  exact (Category.id_comp _).symm

theorem row_normalization : TripleTotal.HorizontalEdge.rightMap S M a wa ≫
    (DoubleCechRegrouping.totalIso U P).hom = DoubleCechGlobalAugmentation.map U P M η := by
  apply HomologicalComplex.Hom.ext
  funext N
  change (((F).map a).f N ≫
    (TripleTotal.RowCoordinates.bicomplex S).ιTotal (.up ℕ) N 0 N rfl) ≫
      (HomologicalComplex₂.total.map (DoubleCechRegrouping.coordinateIso U P).hom (.up ℕ)).f N = _
  erw [Category.assoc, HomologicalComplex₂.ιTotal_map, ← Category.assoc]
  have hN := congrArg (fun f => f.f N) (zeroMap U P M η)
  change ((F).map a).f N ≫ ((coefficientIso U P).hom.f 0).f N =
    (GeometricComparison.CechCone.Total.CechConeTotal.zeroMap U (P ⋙ F) ((F).obj M) (cone P M η)).f N at hN
  exact congrArg (fun m => m ≫ (GeometricComparison.CechCone.Total.CechConeTotal.bicomplex U (P ⋙ F)).ιTotal
    (.up ℕ) N 0 N rfl) hN

theorem comparison : TripleTotal.HorizontalEdge.leftMap S M a wa ≫
    DoubleCechRegrouping.map U P = DoubleCechGlobalAugmentation.map U P M η := by
  change TripleTotal.HorizontalEdge.leftMap S M a wa ≫
    (TripleTotal.RowCoordinates.regroup S ≫ (DoubleCechRegrouping.totalIso U P).hom) = _
  erw [← Category.assoc, TripleTotal.HorizontalEdge.comparison]
  exact row_normalization U P M η

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.DoubleCechGlobalAugmentation
