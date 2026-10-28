import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-! # Proper Product -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.ProperProduct.Construction.FiniteProperProduct

noncomputable section

/-! Finite products of proper schemes over a fixed base, with explicit
projections and the map determined by a family of component maps. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.CategoryTheory.Limits

universe u

variable {S : Scheme.{u}}

def product : {n : ℕ} → (Fin n → Over S) → Over S
  | 0, _ => Over.mk (𝟙 S)
  | _ + 1, P => Over.mk (pullback.fst (P 0).hom (product (fun i => P i.succ)).hom ≫ (P 0).hom)

def first {n : ℕ} (P : Fin (n + 1) → Over S) : FiniteProperProduct.product P ⟶ P 0 :=
  Over.homMk (pullback.fst _ _)

def rest {n : ℕ} (P : Fin (n + 1) → Over S) : FiniteProperProduct.product P ⟶ FiniteProperProduct.product (fun i => P i.succ) :=
  Over.homMk (pullback.snd _ _) (pullback.condition.symm)

def projection : {n : ℕ} → (P : Fin n → Over S) → (i : Fin n) → (FiniteProperProduct.product P ⟶ P i)
  | 0, _, i => Fin.elim0 i
  | _ + 1, P, i => Fin.cases (first P) (fun k => rest P ≫ projection (fun i => P i.succ) k) i

def lift {T : Over S} : {n : ℕ} → (P : Fin n → Over S) → (∀ i, T ⟶ P i) → (T ⟶ FiniteProperProduct.product P)
  | 0, _, _ => Over.homMk T.hom (Category.comp_id _)
  | _ + 1, P, a => Over.homMk
      (pullback.lift (a 0).left (lift (fun i => P i.succ) (fun i => a i.succ)).left
        ((Over.w (a 0)).trans (Over.w _).symm))
      (by
        change _ ≫ pullback.fst _ _ ≫ (P 0).hom = T.hom
        rw [pullback.lift_fst_assoc]
        exact Over.w (a 0))

theorem lift_first {T : Over S} {n : ℕ} (P : Fin (n + 1) → Over S) (a : ∀ i, T ⟶ P i) :
    FiniteProperProduct.lift P a ≫ first P = a 0 := by
  ext1
  exact pullback.lift_fst _ _ _

theorem lift_rest {T : Over S} {n : ℕ} (P : Fin (n + 1) → Over S) (a : ∀ i, T ⟶ P i) :
    FiniteProperProduct.lift P a ≫ rest P = FiniteProperProduct.lift (fun i => P i.succ) (fun i => a i.succ) := by
  ext1
  exact pullback.lift_snd _ _ _

theorem lift_projection {T : Over S} {n : ℕ} (P : Fin n → Over S) (a : ∀ i, T ⟶ P i) (i : Fin n) :
    FiniteProperProduct.lift P a ≫ FiniteProperProduct.projection P i = a i := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    refine Fin.cases ?_ (fun k => ?_) i
    · exact lift_first P a
    · change FiniteProperProduct.lift P a ≫ rest P ≫ FiniteProperProduct.projection (fun i => P i.succ) k = a k.succ
      rw [← Category.assoc, lift_rest]
      exact ih _ _ _

theorem proper {n : ℕ} (P : Fin n → Over S) (hP : ∀ i, IsProper (P i).hom) :
    IsProper (FiniteProperProduct.product P).hom := by
  induction n with
  | zero => exact inferInstanceAs (IsProper (𝟙 S))
  | succ n ih =>
    have := hP 0
    have := ih (fun i => P i.succ) (fun i => hP i.succ)
    change IsProper (pullback.fst (P 0).hom (FiniteProperProduct.product (fun i => P i.succ)).hom ≫ (P 0).hom)
    infer_instance

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.ProperProduct.Construction.FiniteProperProduct
