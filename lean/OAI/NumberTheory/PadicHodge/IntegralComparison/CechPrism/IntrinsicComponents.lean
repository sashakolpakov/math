import OAI.NumberTheory.PadicHodge.IntegralComparison.CechPrism.Components
import Mathlib.Algebra.Homology.HomologicalComplexLimits
import Mathlib.Algebra.Homology.TotalComplex
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-! # Intrinsic Components -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.CechPrism.IntrinsicComponents.Intrinsic

noncomputable section

/-! The prism components as morphisms into the original categorical
double Čech complex. The only change of coordinates is evaluation of
the genuine product of complexes. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite

universe u v w t
variable {C : Type u} [SemilatticeInf C]
  {A : Type v} [Category.{w} A] [Abelian A] [HasProducts.{t} A]
  {ι : Type t} [Finite ι] (U : ι → C)
  (Q : Cᵒᵖ ⥤ A) (B : Cᵒᵖ ⥤ Cᵒᵖ ⥤ A)
  (γ : (Functor.const Cᵒᵖ).obj Q ⟶ B)
  (h : ∀ I V : C, IsIso ((B.obj (op V)).map
    (homOfLE (inf_le_left : I ⊓ V ≤ I)).op))

def complex : HomologicalComplex₂ A (.up ℕ) (.up ℕ) :=
  HomologicalComplex₂.flip ((NonemptyCechNerve.complexFunctor U).obj
    (B ⋙ NonemptyCechNerve.complexFunctor U))

def coordinates (m n : ℕ) : ((complex U B).X m).X n ≅
    Components.target U B m n := by
  letI : PreservesLimitsOfShape (Discrete (Fin (n + 1) → ι))
      (HomologicalComplex.eval A (.up ℕ) m) := inferInstance
  exact PreservesProduct.iso (HomologicalComplex.eval A (.up ℕ) m)
    (fun b : Fin (n + 1) → ι =>
      (NonemptyCechNerve.complexFunctor U).obj (B.obj (op (∏ᶜ (U ∘ b)))))

def projection (m n : ℕ) (a : Fin (m + 1) → ι) (b : Fin (n + 1) → ι) :
    ((complex U B).X m).X n ⟶
      (B.obj (op (∏ᶜ (U ∘ b)))).obj (op (∏ᶜ (U ∘ a))) :=
  (Pi.π (fun b : Fin (n + 1) → ι =>
      (NonemptyCechNerve.complexFunctor U).obj (B.obj (op (∏ᶜ (U ∘ b))))) b).f m ≫
    NonemptyCechDifferential.projection U (B.obj (op (∏ᶜ (U ∘ b)))) m a

def map (m n : ℕ) :
    ((NonemptyCechNerve.complexFunctor U).obj Q).X (m + n + 1) ⟶
      ((complex U B).X m).X n :=
  Components.map U Q B γ h m n ≫ (coordinates U B m n).inv

theorem coordinates_projection (m n : ℕ) (a : Fin (m + 1) → ι) (b : Fin (n + 1) → ι) :
    (coordinates U B m n).hom ≫
      Pi.π (fun b : Fin (n + 1) → ι =>
        ∏ᶜ (fun a : Fin (m + 1) → ι =>
          (B.obj (op (∏ᶜ (U ∘ b)))).obj (op (∏ᶜ (U ∘ a))))) b ≫
      Pi.π (fun a : Fin (m + 1) → ι =>
        (B.obj (op (∏ᶜ (U ∘ b)))).obj (op (∏ᶜ (U ∘ a)))) a =
      projection U B m n a b := by
  exact piComparison_comp_π_assoc (HomologicalComplex.eval A (.up ℕ) m)
    (fun b : Fin (n + 1) → ι =>
      (NonemptyCechNerve.complexFunctor U).obj (B.obj (op (∏ᶜ (U ∘ b))))) b
    (NonemptyCechDifferential.projection U (B.obj (op (∏ᶜ (U ∘ b)))) m a)

theorem map_projection (m n : ℕ) (a : Fin (m + 1) → ι) (b : Fin (n + 1) → ι) :
    Intrinsic.map U Q B γ h m n ≫ projection U B m n a b =
      Components.component U Q B γ h m n a b := by
  rw [← coordinates_projection]
  dsimp only [Intrinsic.map]
  rw [Category.assoc, Iso.inv_hom_id_assoc]
  exact Components.map_projection U Q B γ h m n a b

theorem hom_ext {V : A} (m n : ℕ) {f g : V ⟶ ((complex U B).X m).X n}
    (hfg : ∀ a b, f ≫ projection U B m n a b = g ≫ projection U B m n a b) : f = g := by
  apply (cancel_mono (coordinates U B m n).hom).mp
  apply Pi.hom_ext
  intro b
  apply Pi.hom_ext
  intro a
  simpa only [Category.assoc, coordinates_projection] using hfg a b

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.CechPrism.IntrinsicComponents.Intrinsic
