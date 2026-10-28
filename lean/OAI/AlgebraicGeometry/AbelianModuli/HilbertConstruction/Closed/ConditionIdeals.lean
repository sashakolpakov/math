import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import Mathlib.CategoryTheory.Subfunctor.Basic

/-! # Condition Ideals -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Closed.ConditionIdeals

noncomputable section

/-!
Recovering defining ideals from closed representable conditions. Agreement on
all scheme-valued tests detects equality of ideals, including nilpotent structure.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem ideal_comap_eq_bot_iff {X Y : Scheme.{u}} (I : Y.IdealSheafData) (f : X ⟶ Y) :
    I.comap f = ⊥ ↔ I ≤ f.ker := by
  rw [← le_bot_iff, ← Scheme.IdealSheafData.le_map_iff_comap_le,
    Scheme.IdealSheafData.map_bot]

theorem ideal_eq_of_vanishing_iff {X : Scheme.{u}} (I J : X.IdealSheafData)
    (h : ∀ (T : Scheme.{u}) (f : T ⟶ X), I.comap f = ⊥ ↔ J.comap f = ⊥) : I = J := by
  have self (K : X.IdealSheafData) : K.comap K.subschemeι = ⊥ :=
    (ideal_comap_eq_bot_iff K K.subschemeι).mpr K.ker_subschemeι.ge
  apply le_antisymm
  · have ht := (ideal_comap_eq_bot_iff I J.subschemeι).mp
      ((h J.subscheme J.subschemeι).mpr (self J))
    rwa [J.ker_subschemeι] at ht
  · have ht := (ideal_comap_eq_bot_iff J I.subschemeι).mp
      ((h I.subscheme I.subschemeι).mp (self I))
    rwa [I.ker_subschemeι] at ht

variable {S : Scheme.{u}} {M : Over S}

structure ClosedConditionModel (P : Subfunctor (yoneda.obj M)) where
  scheme : Over S
  inclusion : scheme ⟶ M
  closed : IsClosedImmersion inclusion.left
  factorization : ∀ (T : Over S) (f : T ⟶ M),
    f ∈ P.obj (.op T) ↔ ∃! g : T ⟶ scheme, g ≫ inclusion = f

attribute [instance] ClosedConditionModel.closed

namespace ClosedConditionModel

variable {P : Subfunctor (yoneda.obj M)} (D : ClosedConditionModel P)

def ideal : M.left.IdealSheafData := D.inclusion.left.ker

theorem ideal_vanish_iff {T : Over S} (f : T ⟶ M) :
    D.ideal.comap f.left = ⊥ ↔ f ∈ P.obj (.op T) := by
  rw [ideal_comap_eq_bot_iff, D.factorization]
  constructor
  · intro h
    let l := IsClosedImmersion.lift D.inclusion.left f.left h
    have hl : l ≫ D.inclusion.left = f.left := IsClosedImmersion.lift_fac _ _ h
    let g : T ⟶ D.scheme := Over.homMk l (by
      rw [← D.inclusion.w, ← Category.assoc, hl]
      exact f.w)
    have hg : g ≫ D.inclusion = f := Over.OverMorphism.ext hl
    have : Mono D.inclusion := Over.mono_of_mono_left D.inclusion
    exact ⟨g, hg, fun g' hg' => (cancel_mono D.inclusion).mp (hg'.trans hg.symm)⟩
  · rintro ⟨g, hg, _⟩
    have hleft : g.left ≫ D.inclusion.left = f.left := congrArg Over.Hom.left hg
    change D.inclusion.left.ker ≤ f.left.ker
    rw [← hleft]
    exact Scheme.Hom.le_ker_comp _ _

end ClosedConditionModel

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Closed.ConditionIdeals
