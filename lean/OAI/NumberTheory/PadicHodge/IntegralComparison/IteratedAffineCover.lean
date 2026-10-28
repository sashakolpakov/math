import OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.SequenceCover
import Mathlib.CategoryTheory.Functor.OfSequence
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.Etale

/-! # Iterated Affine Cover -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.IteratedAffineCover

noncomputable section

/-! An affine cover carrying compatible lifts through every iterate of
a finite étale surjective self-map. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u
variable {X U : Scheme.{u}} (f : X ⟶ X) [IsFinite f] [Etale f] [Surjective f]
  (w : U ⟶ X) [IsAffine U]

def stage : ℕ → Over X
  | 0 => Over.mk w
  | n + 1 => (Over.pullback f).obj (stage n)

def step (n : ℕ) : (IteratedAffineCover.stage f w (n + 1)).left ⟶ (IteratedAffineCover.stage f w n).left :=
  pullback.fst (IteratedAffineCover.stage f w n).hom f

omit [IsFinite f] [Etale f] [Surjective f] [IsAffine U] in
theorem step_condition (n : ℕ) :
    (IteratedAffineCover.stage f w (n + 1)).hom ≫ f = IteratedAffineCover.step f w n ≫ (IteratedAffineCover.stage f w n).hom := by
  exact pullback.condition.symm

instance step_finite (n : ℕ) : IsFinite (IteratedAffineCover.step f w n) := by
  unfold IteratedAffineCover.step
  infer_instance

instance step_etale (n : ℕ) : Etale (IteratedAffineCover.step f w n) := by
  unfold IteratedAffineCover.step
  infer_instance

instance step_surjective (n : ℕ) : Surjective (IteratedAffineCover.step f w n) := by
  unfold IteratedAffineCover.step
  infer_instance

instance stage_affine (n : ℕ) : IsAffine (IteratedAffineCover.stage f w n).left := by
  induction n with
  | zero => exact inferInstanceAs (IsAffine U)
  | succ n ih => exact isAffine_of_isAffineHom (IteratedAffineCover.step f w n)

def diagram : ℕᵒᵖ ⥤ Scheme.{u} :=
  Functor.ofOpSequence (X := fun n => (IteratedAffineCover.stage f w n).left) (IteratedAffineCover.step f w)

instance diagram_affine (n : ℕᵒᵖ) : IsAffine ((diagram f w).obj n) := stage_affine f w n.unop

omit [IsFinite f] [IsAffine U] in
theorem diagram_map (i j : ℕ) (h : i ≤ j) :
    Etale ((diagram f w).map (homOfLE h).op) ∧
      Surjective ((diagram f w).map (homOfLE h).op) := by
  induction j, h using Nat.le_induction with
  | base =>
    have he : (diagram f w).map (homOfLE (Nat.le_refl i)).op = 𝟙 _ := (diagram f w).map_id _
    rw [he]
    exact ⟨inferInstance, inferInstance⟩
  | succ j h ih =>
    have he : (homOfLE (Nat.le.step h)).op =
        (homOfLE (Nat.le_succ j)).op ≫ (homOfLE h).op := Subsingleton.elim _ _
    rw [he, Functor.map_comp]
    have hs : (diagram f w).map (homOfLE (Nat.le_succ j)).op = IteratedAffineCover.step f w j :=
      Functor.ofOpSequence_map_homOfLE_succ _ j
    rw [hs]
    let : Etale ((diagram f w).map (homOfLE h).op) := ih.1
    let : Surjective ((diagram f w).map (homOfLE h).op) := ih.2
    exact ⟨inferInstance, inferInstance⟩

def point : Scheme.{u} := Affine.SequenceCover.point (diagram f w)

def projection (n : ℕ) : point f w ⟶ (IteratedAffineCover.stage f w n).left :=
  Affine.SequenceCover.projection (diagram f w) n

omit [Etale f] [Surjective f] in
theorem projection_step (n : ℕ) : projection f w (n + 1) ≫ IteratedAffineCover.step f w n = projection f w n := by
  change Affine.SequenceCover.projection (diagram f w) (n + 1) ≫ IteratedAffineCover.step f w n =
    Affine.SequenceCover.projection (diagram f w) n
  have he := Affine.SequenceCover.projection_comp (diagram f w) n (n + 1) (Nat.le_succ n)
  rw [show (diagram f w).map (homOfLE (Nat.le_succ n)).op = IteratedAffineCover.step f w n from
    Functor.ofOpSequence_map_homOfLE_succ _ n] at he
  exact he

def toBase (n : ℕ) : point f w ⟶ X := projection f w n ≫ (IteratedAffineCover.stage f w n).hom

omit [Etale f] [Surjective f] in
theorem toBase_step (n : ℕ) : toBase f w (n + 1) ≫ f = toBase f w n := by
  rw [toBase, toBase, Category.assoc, step_condition, ← Category.assoc, projection_step]

instance point_affine : IsAffine (point f w) :=
  inferInstanceAs (IsAffine (Affine.SequenceCover.point (diagram f w)))

theorem projection_zero_surjective : Surjective (projection f w 0) :=
  Affine.SequenceCover.projection_surjective (diagram f w) (fun i j h =>
    let he := diagram_map f w i j h
    letI : Etale ((diagram f w).map (homOfLE h).op) := he.1
    ⟨inferInstance, he.2⟩)

theorem projection_zero_weaklyEtale : WeaklyEtale (projection f w 0) :=
  Affine.SequenceCover.projection_weaklyEtale (diagram f w) (fun i j h =>
    let he := diagram_map f w i j h
    letI : Etale ((diagram f w).map (homOfLE h).op) := he.1
    ⟨inferInstance, he.2⟩) (fun n => by
      let : Etale ((diagram f w).map (homOfLE (Nat.zero_le n)).op) :=
        (diagram_map f w 0 n (Nat.zero_le n)).1
      infer_instance)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.IteratedAffineCover
