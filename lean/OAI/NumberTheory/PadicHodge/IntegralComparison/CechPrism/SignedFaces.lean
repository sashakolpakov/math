import OAI.NumberTheory.PadicHodge.IntegralComparison.CechPrism.Faces
import OAI.NumberTheory.PadicHodge.IntegralComparison.TotalHomotopyAssembly

/-! # Signed Faces -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.CechPrism.SignedFaces

noncomputable section

/-! Degree transports and the actual totalization sign for the three
prism differential components. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.Preadditive Opposite

universe u v w t
variable {C : Type u} [SemilatticeInf C]
  {A : Type v} [Category.{w} A] [Abelian A] [HasProducts.{t} A]
  {ι : Type t} [Finite ι] (U : ι → C)
  (Q : Cᵒᵖ ⥤ A) (B : Cᵒᵖ ⥤ Cᵒᵖ ⥤ A)
  (γ : (Functor.const Cᵒᵖ).obj Q ⟶ B)
  (h : ∀ I V : C, IsIso ((B.obj (op V)).map
    (homOfLE (inf_le_left : I ⊓ V ≤ I)).op))

open OAI.NumberTheory.PadicHodge.IntegralComparison.CechPrism.IntrinsicComponents.Intrinsic OAI.NumberTheory.PadicHodge.IntegralComparison.CechPrism.EvaluationNaturality
local notation "K" => Functor.obj (OAI.NumberTheory.PadicHodge.IntegralComparison.NonemptyCechNerve.complexFunctor U) Q

def component (N p q : ℕ) (hpq : p + q = N) : (K).X (N + 1) ⟶ ((IntrinsicComponents.Intrinsic.complex U B).X p).X q :=
  TotalHomotopyAssembly.signedComponent K (IntrinsicComponents.Intrinsic.complex U B) (IntrinsicComponents.Intrinsic.map U Q B γ h) N p q hpq

theorem self (p q : ℕ) : component U Q B γ h (p + q) p q rfl =
    (-1 : ℤ)^p • IntrinsicComponents.Intrinsic.map U Q B γ h p q :=
  TotalHomotopyAssembly.signedComponent_self K (IntrinsicComponents.Intrinsic.complex U B) (IntrinsicComponents.Intrinsic.map U Q B γ h) p q

theorem source (N p q : ℕ) (hpq : p + q = N)
    (a : Fin (p + 1) → ι) (b : Fin (q + 1) → ι) :
    (K).d N (N + 1) ≫ component U Q B γ h N p q hpq ≫ IntrinsicComponents.Intrinsic.projection U B p q a b =
      (-1 : ℤ)^p • Cech.TupleConcatenation.boundaryValue
        (EvaluationNaturality.value U Q B γ h (∏ᶜ (U ∘ a)) (∏ᶜ (U ∘ b)) N)
        (List.ofFn a ++ List.ofFn b) := by
  subst N
  rw [self, zsmul_comp, comp_zsmul, Faces.source]

theorem inner (N p q : ℕ) (hpq : p + q = N)
    (a : Fin (p + 2) → ι) (b : Fin (q + 1) → ι) :
    component U Q B γ h N p q hpq ≫ ((IntrinsicComponents.Intrinsic.complex U B).d p (p + 1)).f q ≫
        IntrinsicComponents.Intrinsic.projection U B (p + 1) q a b =
      (-1 : ℤ)^p • Cech.TupleConcatenation.boundaryValue
        (fun l => EvaluationNaturality.value U Q B γ h (∏ᶜ (U ∘ a)) (∏ᶜ (U ∘ b)) (N + 1)
          (l ++ List.ofFn b)) (List.ofFn a) := by
  subst N
  rw [self, zsmul_comp, Faces.inner,
    Cech.FiniteTupleConcatenation.boundaryValue_eq]

theorem outer (N p q : ℕ) (hpq : p + q = N)
    (a : Fin (p + 1) → ι) (b : Fin (q + 2) → ι) :
    component U Q B γ h N p q hpq ≫ ((IntrinsicComponents.Intrinsic.complex U B).X p).d q (q + 1) ≫
        IntrinsicComponents.Intrinsic.projection U B p (q + 1) a b =
      (-1 : ℤ)^p • Cech.TupleConcatenation.boundaryValue
        (fun l => EvaluationNaturality.value U Q B γ h (∏ᶜ (U ∘ a)) (∏ᶜ (U ∘ b)) (N + 1)
          (List.ofFn a ++ l)) (List.ofFn b) := by
  subst N
  rw [self, zsmul_comp, Faces.outer,
    Cech.FiniteTupleConcatenation.boundaryValue_eq]

theorem outer_signed (N p q : ℕ) (hpq : p + q = N)
    (a : Fin (p + 1) → ι) (b : Fin (q + 2) → ι) :
    ((-1 : ℤˣ)^p) • (component U Q B γ h N p q hpq ≫
        ((IntrinsicComponents.Intrinsic.complex U B).X p).d q (q + 1) ≫ IntrinsicComponents.Intrinsic.projection U B p (q + 1) a b) =
      Cech.TupleConcatenation.boundaryValue
        (fun l => EvaluationNaturality.value U Q B γ h (∏ᶜ (U ∘ a)) (∏ᶜ (U ∘ b)) (N + 1)
          (List.ofFn a ++ l)) (List.ofFn b) := by
  rw [outer]
  simp only [Units.smul_def, Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one]
  rw [smul_smul, ← mul_pow]
  norm_num

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.CechPrism.SignedFaces
