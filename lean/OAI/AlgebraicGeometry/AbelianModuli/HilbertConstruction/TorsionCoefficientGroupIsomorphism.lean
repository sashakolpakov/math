import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fintype.EquivFin
import Mathlib.LinearAlgebra.Pi

/-! # Torsion Coefficient Group Isomorphism -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.TorsionCoefficientGroupIsomorphism

noncomputable section

/-! A finite family of torsion elements defines its actual homomorphism
from the finite constant coefficient group. Generation gives surjectivity,
and the expected cardinality then gives an additive isomorphism. -/
open scoped BigOperators Classical
universe u v
variable {G : Type u} [AddCommGroup G]

def integerMultipleHom (x : G) : ℤ →+ G where
  toFun a := a • x
  map_zero' := zero_zsmul x
  map_add' a b := by simp only [add_zsmul]

def torsionCoefficientHom (n : ℕ) (x : G) (hx : (n : ℤ) • x = 0) : ZMod n →+ G :=
  ZMod.lift n ⟨integerMultipleHom x, hx⟩

theorem torsionCoefficientHom_intCast (n : ℕ) (x : G) (hx : (n : ℤ) • x = 0) (a : ℤ) :
    torsionCoefficientHom n x hx (a : ZMod n) = a • x :=
  ZMod.lift_coe n ⟨integerMultipleHom x, hx⟩ a

variable {ι : Type v} [Fintype ι] (n : ℕ) (v : ι → G) (hv : ∀ i, (n : ℤ) • v i = 0)

def torsionLabelCombination : (ι → ZMod n) →+ G where
  toFun c := ∑ i, torsionCoefficientHom n (v i) (hv i) (c i)
  map_zero' := by simp only [Pi.zero_apply, map_zero, Finset.sum_const_zero]
  map_add' a b := by simp only [Pi.add_apply, map_add, Finset.sum_add_distrib]

theorem torsionLabelCombination_intCast (c : ι → ℤ) :
    torsionLabelCombination n v hv (fun i => (c i : ZMod n)) = ∑ i, c i • v i := by
  change (∑ i, torsionCoefficientHom n (v i) (hv i) (c i : ZMod n)) = _
  apply Finset.sum_congr rfl
  intro i _
  exact torsionCoefficientHom_intCast n (v i) (hv i) (c i)

theorem torsionLabelCombination_surjective
    (h : ∀ x : G, ∃ c : ι → ℤ, ∑ i, c i • v i = x) :
    Function.Surjective (torsionLabelCombination n v hv) := by
  intro x
  obtain ⟨c, hc⟩ := h x
  exact ⟨fun i => (c i : ZMod n), (torsionLabelCombination_intCast n v hv c).trans hc⟩

def torsionLabelEquiv [NeZero n] [Fintype G]
    (h : ∀ x : G, ∃ c : ι → ℤ, ∑ i, c i • v i = x)
    (hcard : Fintype.card G = n ^ Fintype.card ι) : (ι → ZMod n) ≃+ G :=
  AddEquiv.ofBijective (torsionLabelCombination n v hv)
    ((Fintype.bijective_iff_surjective_and_card _).mpr
      ⟨torsionLabelCombination_surjective n v hv h,
        (by simpa only [Fintype.card_fun, ZMod.card] using hcard.symm)⟩)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.TorsionCoefficientGroupIsomorphism
