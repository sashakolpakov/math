import OAI.AlgebraicGeometry.HilbertScheme.Presentations.BaseProjectivePresentation
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.ExactSegrePresentation

/-! # Parameter Products -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Finite.ParameterProducts.Core

noncomputable section

/-! Finite parameter products with explicit projections and lifts,
including a projective presentation constructed by iterated Segre embeddings. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u
variable {S : Scheme.{u}}

def finiteParameterProduct : (n : ℕ) → (Fin n → Over S) → Over S
  | 0, _ => Over.mk (𝟙 S)
  | n + 1, H => H 0 ⨯ finiteParameterProduct n (fun i => H i.succ)

def finiteParameterProjection : {n : ℕ} → (H : Fin n → Over S) →
    (i : Fin n) → (Core.finiteParameterProduct n H ⟶ H i)
  | 0, _, i => Fin.elim0 i
  | n + 1, H, i => Fin.cases prod.fst
      (fun k => prod.snd ≫ finiteParameterProjection (fun j : Fin n => H j.succ) k) i

def finiteParameterLift {T : Over S} : {n : ℕ} → (H : Fin n → Over S) →
    (∀ i, T ⟶ H i) → (T ⟶ Core.finiteParameterProduct n H)
  | 0, _, _ => Over.homMk T.hom (Category.comp_id T.hom)
  | n + 1, H, f => prod.lift (f 0)
      (finiteParameterLift (fun i : Fin n => H i.succ) (fun i => f i.succ))

theorem finiteParameterLift_projection {T : Over S} {n : ℕ} (H : Fin n → Over S)
    (f : ∀ i, T ⟶ H i) (i : Fin n) :
    Core.finiteParameterLift H f ≫ Core.finiteParameterProjection H i = f i := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    refine Fin.cases ?_ (fun k => ?_) i
    · exact prod.lift_fst _ _
    · change prod.lift (f 0) (Core.finiteParameterLift (fun j : Fin n => H j.succ)
        (fun j => f j.succ)) ≫
        (prod.snd ≫ Core.finiteParameterProjection (fun j : Fin n => H j.succ) k) = f k.succ
      rw [prod.lift_snd_assoc]
      exact ih _ _ _

theorem finiteParameter_hom_ext {T : Over S} {n : ℕ} (H : Fin n → Over S)
    (f g : T ⟶ Core.finiteParameterProduct n H)
    (h : ∀ i, f ≫ Core.finiteParameterProjection H i = g ≫ Core.finiteParameterProjection H i) : f = g := by
  induction n with
  | zero =>
    apply Over.OverMorphism.ext
    exact (Category.comp_id (show T.left ⟶ S from f.left)).symm.trans
      (f.w.trans (g.w.symm.trans (Category.comp_id (show T.left ⟶ S from g.left))))
  | succ n ih =>
    apply prod.hom_ext
    · exact h 0
    · apply ih
      intro i
      have hi := h i.succ
      change f ≫ (prod.snd ≫ Core.finiteParameterProjection (fun j : Fin n => H j.succ) i) =
        g ≫ (prod.snd ≫ Core.finiteParameterProjection (fun j : Fin n => H j.succ) i) at hi
      exact (Category.assoc f prod.snd (Core.finiteParameterProjection (fun j : Fin n => H j.succ) i)).trans
        (hi.trans (Category.assoc g prod.snd (Core.finiteParameterProjection (fun j : Fin n => H j.succ) i)).symm)

def finiteParameterProjectivePresentation : {n : ℕ} → (H : Fin n → Over S) →
    (∀ i, Has.Core.ProjectivePresentation (H i)) → Has.Core.ProjectivePresentation (Core.finiteParameterProduct n H)
  | 0, _, _ => BaseProjectivePresentation.Core.baseProjectivePresentation S
  | n + 1, H, B => Relative.SegrePresentation.Core.segreProductPresentation (B 0)
      (finiteParameterProjectivePresentation (fun i : Fin n => H i.succ) (fun i => B i.succ))

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Finite.ParameterProducts.Core
