import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polarized.ReverseFiniteHomomorphism

/-! # Multiplication Finite -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! The constructed finite reverse polarization shows that every
positive multiplication map on the dual is finite over the original base. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj
universe u
variable {S : Scheme.{u}} {g N : ℕ} {δ : Fin g → ℕ}
variable (A : PolarizationData.PolarizedAbelianWithFullLevel g δ N S) (hδ : ∀ i, 0 < δ i)

include hδ

theorem PolarizationData.PolarizedAbelianWithFullLevel.dual_multiplication_isFinite (n : ℕ) (hn : 0 < n) :
    IsFinite (A.dual.abelian.multiplication n).left := by
  obtain ⟨m, hm, hfin, _, _⟩ := A.exists_finite_reverseHomomorphism hδ
  let : IsMonHom m := hm
  let : IsFinite m.left := hfin
  let : IsFinite (A.abelian.multiplication n).left := A.multiplication_isFinite n hn
  have hc : A.dual.abelian.multiplication n ≫ m = m ≫ A.abelian.multiplication n := by
    calc
      A.dual.abelian.multiplication n ≫ m = m ^ n := by
        change ((𝟙 A.dual.abelian.scheme) ^ n) ≫ m = m ^ n
        rw [MonObj.pow_comp, Category.id_comp]
      _ = m ≫ A.abelian.multiplication n := (A.abelian.comp_multiplication n m).symm
  have : IsFinite ((A.dual.abelian.multiplication n).left ≫ m.left) := by
    change IsFinite (A.dual.abelian.multiplication n ≫ m).left
    rw [hc]
    exact inferInstanceAs (IsFinite (m.left ≫ (A.abelian.multiplication n).left))
  exact IsFinite.of_comp (A.dual.abelian.multiplication n).left m.left

theorem PolarizationData.PolarizedAbelianWithFullLevel.dual_torsionScheme_isFinite (n : ℕ) (hn : 0 < n) :
    IsFinite (A.dual.abelian.torsionScheme n).hom := by
  let : IsFinite (A.dual.abelian.multiplication n).left := A.dual_multiplication_isFinite hδ n hn
  exact inferInstanceAs
    (IsFinite (pullback.snd (A.dual.abelian.multiplication n).left η[A.dual.abelian.scheme].left))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
