import OAI.NumberTheory.PadicHodge.IntegralComparison.CechPrism.SignedFaces
import OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.FiniteTupleConcatenation

/-! # Homotopy -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.CechPrism.Homotopy

noncomputable section

/-! The signed concatenation homotopy between the two native Čech
augmentations, characterized by their actual tuple projections. -/

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
open OAI.NumberTheory.PadicHodge.IntegralComparison.CechPrism.EvaluationNaturality (value)
open OAI.NumberTheory.PadicHodge.IntegralComparison.CechPrism.SignedFaces
variable [(IntrinsicComponents.Intrinsic.complex U B).HasTotal (.up ℕ)] (f g : ((NonemptyCechNerve.complexFunctor U).obj Q) ⟶ (IntrinsicComponents.Intrinsic.complex U B).total (.up ℕ))
  (hfg : ∀ N p q (_hpq : p + q = N) (a : Fin (p + 1) → ι) (b : Fin (q + 1) → ι),
    (f.f N - g.f N) ≫ (AlgebraicGeometry.SheafCohomology.Cech.UpNatLowDegrees.HomologicalComplex₂.πTotalUpNat (complex U B)) p q N ≫ IntrinsicComponents.Intrinsic.projection U B p q a b =
      (if p = 0 then EvaluationNaturality.value U Q B γ h (∏ᶜ (U ∘ a)) (∏ᶜ (U ∘ b)) N (List.ofFn b) else 0) -
        (if q = 0 then EvaluationNaturality.value U Q B γ h (∏ᶜ (U ∘ a)) (∏ᶜ (U ∘ b)) N (List.ofFn a) else 0))

include hfg

theorem zero : (f.f 0 - g.f 0) ≫ (AlgebraicGeometry.SheafCohomology.Cech.UpNatLowDegrees.HomologicalComplex₂.πTotalUpNat (complex U B)) 0 0 0 =
    ((NonemptyCechNerve.complexFunctor U).obj Q).d 0 1 ≫ SignedFaces.component U Q B γ h 0 0 0 rfl := by
  apply IntrinsicComponents.Intrinsic.hom_ext U B 0 0
  intro a b
  rw [Category.assoc, hfg 0 0 0 rfl a b, Category.assoc, SignedFaces.source]
  simp only [pow_zero, one_smul]
  exact (Cech.FiniteTupleConcatenation.PrismCancellation.zero
    (EvaluationNaturality.value U Q B γ h (∏ᶜ (U ∘ a)) (∏ᶜ (U ∘ b)) 0) a b).symm

theorem left (n : ℕ) : (f.f (n + 1) - g.f (n + 1)) ≫ (AlgebraicGeometry.SheafCohomology.Cech.UpNatLowDegrees.HomologicalComplex₂.πTotalUpNat (complex U B)) 0 (n + 1) (n + 1) =
    ((NonemptyCechNerve.complexFunctor U).obj Q).d (n + 1) (n + 2) ≫ SignedFaces.component U Q B γ h (n + 1) 0 (n + 1) (by omega) +
      SignedFaces.component U Q B γ h n 0 n (by omega) ≫ ((IntrinsicComponents.Intrinsic.complex U B).X 0).d n (n + 1) := by
  apply IntrinsicComponents.Intrinsic.hom_ext U B 0 (n + 1)
  intro a b
  rw [Category.assoc, hfg (n + 1) 0 (n + 1) (by omega) a b, add_comp,
    Category.assoc, SignedFaces.source, Category.assoc, SignedFaces.outer]
  simp only [Nat.add_one_ne_zero, ite_false, sub_zero, pow_zero, one_smul]
  exact (Cech.FiniteTupleConcatenation.PrismCancellation.left
    (EvaluationNaturality.value U Q B γ h (∏ᶜ (U ∘ a)) (∏ᶜ (U ∘ b)) (n + 1)) n a b).symm

theorem right (n : ℕ) : (f.f (n + 1) - g.f (n + 1)) ≫ (AlgebraicGeometry.SheafCohomology.Cech.UpNatLowDegrees.HomologicalComplex₂.πTotalUpNat (complex U B)) (n + 1) 0 (n + 1) =
    ((NonemptyCechNerve.complexFunctor U).obj Q).d (n + 1) (n + 2) ≫ SignedFaces.component U Q B γ h (n + 1) (n + 1) 0 (by omega) +
      SignedFaces.component U Q B γ h n n 0 (by omega) ≫ ((IntrinsicComponents.Intrinsic.complex U B).d n (n + 1)).f 0 := by
  apply IntrinsicComponents.Intrinsic.hom_ext U B (n + 1) 0
  intro a b
  rw [Category.assoc, hfg (n + 1) (n + 1) 0 (by omega) a b, add_comp,
    Category.assoc, SignedFaces.source, Category.assoc, SignedFaces.inner]
  simp only [Nat.add_one_ne_zero, ite_false, zero_sub]
  exact (Cech.FiniteTupleConcatenation.PrismCancellation.right
    (EvaluationNaturality.value U Q B γ h (∏ᶜ (U ∘ a)) (∏ᶜ (U ∘ b)) (n + 1)) n a b).symm

theorem interior (p q : ℕ) :
    (f.f (p + q + 2) - g.f (p + q + 2)) ≫ (AlgebraicGeometry.SheafCohomology.Cech.UpNatLowDegrees.HomologicalComplex₂.πTotalUpNat (complex U B)) (p + 1) (q + 1) (p + q + 2) =
      ((NonemptyCechNerve.complexFunctor U).obj Q).d (p + q + 2) (p + q + 3) ≫
        SignedFaces.component U Q B γ h (p + q + 2) (p + 1) (q + 1) (by omega) +
      (SignedFaces.component U Q B γ h (p + q + 1) p (q + 1) (by omega) ≫ ((IntrinsicComponents.Intrinsic.complex U B).d p (p + 1)).f (q + 1) +
        ((-1 : ℤˣ)^(p + 1)) •
          (SignedFaces.component U Q B γ h (p + q + 1) (p + 1) q (by omega) ≫ ((IntrinsicComponents.Intrinsic.complex U B).X (p + 1)).d q (q + 1))) := by
  apply IntrinsicComponents.Intrinsic.hom_ext U B (p + 1) (q + 1)
  intro a b
  rw [Category.assoc, hfg (p + q + 2) (p + 1) (q + 1) (by omega) a b,
    add_comp, add_comp, Category.assoc, SignedFaces.source, Category.assoc, SignedFaces.inner,
    Linear.units_smul_comp, Category.assoc, SignedFaces.outer_signed]
  simp only [Nat.add_one_ne_zero, ite_false, sub_self]
  exact (Cech.FiniteTupleConcatenation.PrismCancellation.interior
    (EvaluationNaturality.value U Q B γ h (∏ᶜ (U ∘ a)) (∏ᶜ (U ∘ b)) (p + q + 2)) p q a b).symm

def data : TotalHomotopyAssembly.Data ((NonemptyCechNerve.complexFunctor U).obj Q) (IntrinsicComponents.Intrinsic.complex U B) f g where
  component := SignedFaces.component U Q B γ h
  zero := CechPrism.Homotopy.zero U Q B γ h f g hfg
  left := CechPrism.Homotopy.left U Q B γ h f g hfg
  right := CechPrism.Homotopy.right U Q B γ h f g hfg
  interior := CechPrism.Homotopy.interior U Q B γ h f g hfg

def homotopy : Homotopy f g :=
  TotalHomotopyAssembly.homotopy ((NonemptyCechNerve.complexFunctor U).obj Q) (IntrinsicComponents.Intrinsic.complex U B) f g (data U Q B γ h f g hfg)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.CechPrism.Homotopy
