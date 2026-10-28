import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.CategoryTheory.Limits.Constructions.Over.Products

/-! # Proper Products -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.ProperProducts

noncomputable section

/-! Finite products of proper schemes over a common base are proper. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

variable {S : Scheme.{u}}

def overFinProductSuccIso {n : ℕ} (F : Fin (n + 1) → Over S) :
    (∏ᶜ F) ≅ F 0 ⨯ ∏ᶜ (fun i : Fin n => F i.succ) where
  hom := prod.lift (Pi.π F 0) (Pi.lift (fun i => Pi.π F i.succ))
  inv := Pi.lift (Fin.cases prod.fst (fun i => prod.snd ≫ Pi.π _ i))
  hom_inv_id := by
    apply Pi.hom_ext
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [Category.assoc, Pi.lift_comp_π, Fin.cases_zero, Category.id_comp]
      exact prod.lift_fst _ _
    · simp only [Category.assoc, Pi.lift_comp_π, Fin.cases_succ, Category.id_comp]
      rw [prod.lift_snd_assoc, Pi.lift_comp_π]
  inv_hom_id := by
    apply prod.hom_ext
    · simp only [Category.assoc, prod.lift_fst, Pi.lift_comp_π, Fin.cases_zero, Category.id_comp]
    · apply Pi.hom_ext
      intro i
      simp only [Category.assoc, prod.lift_snd_assoc, Pi.lift_comp_π, Fin.cases_succ, Category.id_comp]

theorem over_proper_of_iso {X Y : Over S} (e : X ≅ Y) [IsProper Y.hom] : IsProper X.hom := by
  have : IsIso e.hom.left := (Over.forget S).map_isIso e.hom
  rw [← e.hom.w]
  infer_instance

theorem overBinaryProduct_proper (X Y : Over S) [IsProper X.hom] [IsProper Y.hom] :
    IsProper (X ⨯ Y).hom := by
  rw [← (prod.fst : X ⨯ Y ⟶ X).w, ← Over.prodLeftIsoPullback_hom_fst]
  infer_instance

def overEmptyProductIso (F : Fin 0 → Over S) : (∏ᶜ F) ≅ Over.mk (𝟙 S) where
  hom := Over.homMk (∏ᶜ F).hom
  inv := Pi.lift (fun i => Fin.elim0 i)
  hom_inv_id := by
    apply Pi.hom_ext
    intro i
    exact Fin.elim0 i
  inv_hom_id := by
    apply (Over.forget S).map_injective
    exact (Pi.lift (fun i => Fin.elim0 i) : Over.mk (𝟙 S) ⟶ ∏ᶜ F).w

theorem overFinProduct_proper (n : ℕ) (F : Fin n → Over S)
    (hF : ∀ i, IsProper (F i).hom) : IsProper (∏ᶜ F).hom := by
  induction n with
  | zero =>
      have : IsProper (Over.mk (𝟙 S)).hom := inferInstanceAs (IsProper (𝟙 S))
      exact over_proper_of_iso (overEmptyProductIso F)
  | succ n ih =>
      have : IsProper (F 0).hom := hF 0
      have : IsProper (∏ᶜ (fun i : Fin n => F i.succ)).hom :=
        ih _ (fun i => hF i.succ)
      have := overBinaryProduct_proper (F 0) (∏ᶜ (fun i : Fin n => F i.succ))
      exact over_proper_of_iso (overFinProductSuccIso F)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.ProperProducts
