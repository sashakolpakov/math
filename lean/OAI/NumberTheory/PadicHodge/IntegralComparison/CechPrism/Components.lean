import OAI.NumberTheory.PadicHodge.IntegralComparison.SemilatticeTupleIntersection
import OAI.NumberTheory.PadicHodge.IntegralComparison.SemilatticeCechAmalgamation
import OAI.NumberTheory.PadicHodge.IntegralComparison.NonemptyCechDifferential

/-! # Components -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.CechPrism.Components

noncomputable section

/-! The concatenation-prism components use the original Čech tuple
products and the genuine inverse-meet coefficient map. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite

universe u v w t
variable {C : Type u} [SemilatticeInf C]
  {A : Type v} [Category.{w} A] [Preadditive A] [HasProducts.{t} A]
  {ι : Type t} (U : ι → C)
  (Q : Cᵒᵖ ⥤ A) (B : Cᵒᵖ ⥤ Cᵒᵖ ⥤ A)
  (γ : (Functor.const Cᵒᵖ).obj Q ⟶ B)
  (h : ∀ I V : C, IsIso ((B.obj (op V)).map
    (homOfLE (inf_le_left : I ⊓ V ≤ I)).op))

def tuple {m n : ℕ} (a : Fin (m + 1) → ι) (b : Fin (n + 1) → ι) :
    Fin (m + n + 1 + 1) → ι :=
  Fin.append a b ∘ Fin.cast (by omega)

theorem product_tuple {m n : ℕ} (a : Fin (m + 1) → ι) (b : Fin (n + 1) → ι) :
    (∏ᶜ (U ∘ tuple a b)) = (∏ᶜ (U ∘ a)) ⊓ (∏ᶜ (U ∘ b)) := by
  have he : (U ∘ tuple a b) = Fin.append (U ∘ a) (U ∘ b) ∘
      (finCongr (by omega : m + n + 1 + 1 = (m + 1) + (n + 1))) := by
    funext i
    change U (Fin.append a b (Fin.cast
      (by omega : m + n + 1 + 1 = (m + 1) + (n + 1)) i)) =
      Fin.append (U ∘ a) (U ∘ b) (Fin.cast
        (by omega : m + n + 1 + 1 = (m + 1) + (n + 1)) i)
    generalize Fin.cast (by omega : m + n + 1 + 1 = (m + 1) + (n + 1)) i = j
    refine Fin.addCases (fun j => ?_) (fun j => ?_) j <;> simp
  rw [he]
  exact (SemilatticeTupleIntersection.product_reindex _ _).trans
    (SemilatticeTupleIntersection.product_append _ _)

abbrev target (m n : ℕ) :=
  ∏ᶜ (fun b : Fin (n + 1) → ι =>
    ∏ᶜ (fun a : Fin (m + 1) → ι =>
      (B.obj (op (∏ᶜ (U ∘ b)))).obj (op (∏ᶜ (U ∘ a)))))

def component (m n : ℕ) (a : Fin (m + 1) → ι) (b : Fin (n + 1) → ι) :
    ((NonemptyCechNerve.complexFunctor U).obj Q).X (m + n + 1) ⟶
      (B.obj (op (∏ᶜ (U ∘ b)))).obj (op (∏ᶜ (U ∘ a))) :=
  NonemptyCechDifferential.projection U Q (m + n + 1) (tuple a b) ≫
    Q.map (eqToHom (congrArg op (product_tuple U a b))) ≫
      SemilatticeCechAmalgamation.map Q B γ h (∏ᶜ (U ∘ a)) (∏ᶜ (U ∘ b))

def map (m n : ℕ) :
    ((NonemptyCechNerve.complexFunctor U).obj Q).X (m + n + 1) ⟶ target U B m n :=
  Pi.lift (fun b => Pi.lift (fun a => component U Q B γ h m n a b))

theorem map_projection (m n : ℕ) (a : Fin (m + 1) → ι) (b : Fin (n + 1) → ι) :
    Components.map U Q B γ h m n ≫
      Pi.π (fun b : Fin (n + 1) → ι =>
        ∏ᶜ (fun a : Fin (m + 1) → ι =>
          (B.obj (op (∏ᶜ (U ∘ b)))).obj (op (∏ᶜ (U ∘ a))))) b ≫
      Pi.π (fun a : Fin (m + 1) → ι =>
        (B.obj (op (∏ᶜ (U ∘ b)))).obj (op (∏ᶜ (U ∘ a)))) a =
      component U Q B γ h m n a b := by
  exact (Pi.lift_comp_π_assoc _ _ _).trans (Pi.lift_comp_π _ _)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.CechPrism.Components
