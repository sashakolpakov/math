import Mathlib.Algebra.Homology.Homotopy

/-! # Lower Homotopy -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Cochain.LowerHomotopy

noncomputable section

/-! A degree-lowering family gives a cochain homotopy from its
degree-zero and successor differential identities. -/

open _root_.CategoryTheory _root_.CategoryTheory.Preadditive

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u v
variable {C : Type u} [Category.{v} C] [Preadditive C]
  (K L : CochainComplex C ℕ) (s : ∀ n, K.X (n + 1) ⟶ L.X n)

def family (i j : ℕ) (h : (ComplexShape.up ℕ).Rel j i) : K.X i ⟶ L.X j := by
  obtain rfl : i = j + 1 := h.symm
  exact s j

theorem family_succ (n : ℕ) : family K L s (n + 1) n rfl = s n := rfl

def boundary : K ⟶ L := Homotopy.nullHomotopicMap' (family K L s)

theorem boundary_zero : (boundary K L s).f 0 = K.d 0 1 ≫ s 0 := by
  unfold boundary
  rw [Homotopy.nullHomotopicMap'_f_of_not_rel_right (k₁ := 0) (k₀ := 1) rfl
    (by intro i hi; change i + 1 = 0 at hi; omega)]
  erw [family_succ]

theorem boundary_succ (n : ℕ) : (boundary K L s).f (n + 1) =
    K.d (n + 1) (n + 2) ≫ s (n + 1) + s n ≫ L.d n (n + 1) := by
  unfold boundary
  rw [Homotopy.nullHomotopicMap'_f (k₂ := n) (k₁ := n + 1) (k₀ := n + 2) rfl rfl]
  erw [family_succ, family_succ]

def homotopy (f g : K ⟶ L)
    (hzero : f.f 0 - g.f 0 = K.d 0 1 ≫ s 0)
    (hsucc : ∀ n, f.f (n + 1) - g.f (n + 1) =
      K.d (n + 1) (n + 2) ≫ s (n + 1) + s n ≫ L.d n (n + 1)) :
    Homotopy f g := by
  have h : f - g = boundary K L s := by
    apply HomologicalComplex.Hom.ext
    funext n
    cases n with
    | zero => exact hzero.trans (boundary_zero K L s).symm
    | succ n => exact (hsucc n).trans (boundary_succ K L s n).symm
  exact (Homotopy.equivSubZero (f := f) (g := g)).symm
    ((Homotopy.ofEq h).trans (Homotopy.nullHomotopy' (family K L s)))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Cochain.LowerHomotopy
