import OAI.NumberTheory.PadicHodge.IntegralComparison.CechPrism.DiagonalComplex
import OAI.NumberTheory.PadicHodge.IntegralComparison.CechPrism.Differentials
import OAI.AlgebraicGeometry.SheafCohomology.Cech.UpNatVerticalEdge
import OAI.AlgebraicGeometry.Comparison.Betti.TotalExists

/-! # Diagonal Augmentation -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.CechPrism.DiagonalAugmentation

noncomputable section

/-! The original local-cone diagonal map is the other augmentation
into the actual double Čech total. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.Preadditive Opposite

universe u v w t
variable {C : Type u} [SemilatticeInf C]
  {A : Type v} [Category.{w} A] [Abelian A] [HasProducts.{t} A]
  {ι : Type t} [Finite ι] (U : ι → C)
  (Q : Cᵒᵖ ⥤ A) (B : Cᵒᵖ ⥤ Cᵒᵖ ⥤ A)
  (γ : (Functor.const Cᵒᵖ).obj Q ⟶ B)
  (h : ∀ I V : C, IsIso ((B.obj (op V)).map
    (homOfLE (inf_le_left : I ⊓ V ≤ I)).op))

open OAI.NumberTheory.PadicHodge.IntegralComparison.CechPrism.IntrinsicComponents.Intrinsic

theorem face (n : ℕ) (a : Fin 2 → ι) (b : Fin (n + 1) → ι) (i : Fin 2) :
    (DiagonalComplex.map U Q B γ h).f n ≫
      IntrinsicComponents.Intrinsic.projection U B 0 n (a ∘ i.succAbove) b ≫
        (B.obj (op (∏ᶜ (U ∘ b)))).map (NonemptyCechDifferential.faceMap U 0 i a).op =
      NonemptyCechDifferential.projection U Q n b ≫
        (γ.app (op (∏ᶜ (U ∘ b)))).app (op (∏ᶜ (U ∘ b))) ≫
          (GeometricComparison.Semilattice.LocalCone.SemilatticeLocalCone.cone C (∏ᶜ (U ∘ b))
            (B.obj (op (∏ᶜ (U ∘ b)))) (fun I => h I (∏ᶜ (U ∘ b)))).app
              (op (∏ᶜ (U ∘ a))) := by
  rw [← Category.assoc, DiagonalComplex.map_projection,
    Category.assoc, Category.assoc]
  have hn := (GeometricComparison.Semilattice.LocalCone.SemilatticeLocalCone.cone C (∏ᶜ (U ∘ b))
    (B.obj (op (∏ᶜ (U ∘ b)))) (fun I => h I (∏ᶜ (U ∘ b)))).naturality
      (NonemptyCechDifferential.faceMap U 0 i a).op
  change 𝟙 _ ≫ _ = _ at hn
  rw [Category.id_comp] at hn
  rw [← hn]

theorem cocycle (n : ℕ) :
    (DiagonalComplex.map U Q B γ h).f n ≫ ((IntrinsicComponents.Intrinsic.complex U B).d 0 1).f n = 0 := by
  apply IntrinsicComponents.Intrinsic.hom_ext U B 1 n
  intro a b
  rw [zero_comp, Category.assoc, Differentials.inner, comp_sum]
  erw [Fin.sum_univ_two]
  simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one,
    one_smul, neg_one_zsmul, comp_neg]
  erw [face, face, add_neg_cancel]

variable [HasFiniteCoproducts A]
local instance total : (IntrinsicComponents.Intrinsic.complex U B).HasTotal (.up ℕ) :=
  AlgebraicGeometry.Comparison.Betti.TotalExists.hasTotal_of_finiteCoproducts _

def map : (NonemptyCechNerve.complexFunctor U).obj Q ⟶ (IntrinsicComponents.Intrinsic.complex U B).total (.up ℕ) :=
  (AlgebraicGeometry.SheafCohomology.Cech.UpNatVerticalEdge.HomologicalComplex₂.totalUpNatVerticalEdge (complex U B)) ((NonemptyCechNerve.complexFunctor U).obj Q)
    (fun n => (DiagonalComplex.map U Q B γ h).f n)
    (fun n m _ => (DiagonalComplex.map U Q B γ h).comm n m)
    (cocycle U Q B γ h)

theorem value_self (n : ℕ) (a : Fin 1 → ι) (b : Fin (n + 1) → ι) :
    (DiagonalAugmentation.map U Q B γ h).f n ≫ (AlgebraicGeometry.SheafCohomology.Cech.UpNatLowDegrees.HomologicalComplex₂.πTotalUpNat (complex U B)) 0 n n ≫ IntrinsicComponents.Intrinsic.projection U B 0 n a b =
      EvaluationNaturality.value U Q B γ h
        (∏ᶜ (U ∘ a)) (∏ᶜ (U ∘ b)) n (List.ofFn b) := by
  rw [DiagonalAugmentation.map, AlgebraicGeometry.SheafCohomology.Cech.UpNatVerticalEdge.HomologicalComplex₂.totalUpNatVerticalEdge_f, Category.assoc,
    AlgebraicGeometry.SheafCohomology.Cech.UpNatLowDegrees.HomologicalComplex₂.ιTotal_πTotalUpNat_assoc]
  simp only [dite_true, HomologicalComplex₂.XXIsoOfEq, eqToIso_refl, Iso.refl_hom,
    Category.id_comp]
  exact DiagonalComplex.value_projection U Q B γ h n a b

theorem value_projection (N p q : ℕ) (hpq : p + q = N)
    (a : Fin (p + 1) → ι) (b : Fin (q + 1) → ι) :
    (DiagonalAugmentation.map U Q B γ h).f N ≫ (AlgebraicGeometry.SheafCohomology.Cech.UpNatLowDegrees.HomologicalComplex₂.πTotalUpNat (complex U B)) p q N ≫ IntrinsicComponents.Intrinsic.projection U B p q a b =
      if p = 0 then EvaluationNaturality.value U Q B γ h
        (∏ᶜ (U ∘ a)) (∏ᶜ (U ∘ b)) N (List.ofFn b) else 0 := by
  by_cases hp : p = 0
  · subst p
    have hN : N = q := by omega
    clear hpq
    subst N
    exact value_self U Q B γ h q a b
  · rw [ite_eq_right hp, DiagonalAugmentation.map, AlgebraicGeometry.SheafCohomology.Cech.UpNatVerticalEdge.HomologicalComplex₂.totalUpNatVerticalEdge_f,
      Category.assoc, AlgebraicGeometry.SheafCohomology.Cech.UpNatLowDegrees.HomologicalComplex₂.ιTotal_πTotalUpNat_assoc]
    simp only [dite_eq_right (Ne.symm hp), zero_comp, comp_zero]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.CechPrism.DiagonalAugmentation
