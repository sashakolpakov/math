import Mathlib.Algebra.Module.ZMod
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-! # Prime Torsion Labels -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.PrimeTorsionLabels

noncomputable section

/-! A finite commutative group killed by a prime, with the proved correct
order, has an actual ordered standard full-level label isomorphism. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem prime_torsion_label_equiv (p d : ℕ) [Fact p.Prime]
    (G : Type) [CommGroup G] (hkill : ∀ x : G, x ^ p = 1)
    (hcard : Nat.card G = p ^ d) : Nonempty (Multiplicative (Fin d → ZMod p) ≃* G) := by
  let V := Additive G
  have : Finite G := Nat.finite_of_card_ne_zero (hcard.trans_ne (pow_ne_zero _ (Fact.out : p.Prime).ne_zero))
  let _ : Fintype G := Fintype.ofFinite G
  let _ : Fintype V := inferInstanceAs (Fintype (Additive G))
  let moduleV : Module (ZMod p) V := AddCommGroup.zmodModule (n := p) (fun x => by
    change x.toMul ^ p = 1
    exact hkill x.toMul)
  have freeV : Module.Free (ZMod p) V := Module.Free.of_divisionRing (ZMod p) V
  have finiteV : Module.Finite (ZMod p) V := Module.Finite.of_finite
  have hd : Module.finrank (ZMod p) V = d := by
    apply Nat.pow_right_injective (Fact.out : p.Prime).one_lt
    calc
      p ^ Module.finrank (ZMod p) V = Fintype.card V := by
        simpa only [ZMod.card] using (Module.card_eq_pow_finrank (K := ZMod p) (V := V)).symm
      _ = p ^ d := by
        change Fintype.card (Additive G) = p ^ d
        rw [Fintype.card_additive, Fintype.card_eq_nat_card]
        exact hcard
  let b : Module.Basis (Fin d) (ZMod p) V := @Module.finBasisOfFinrankEq
    (ZMod p) V inferInstance inferInstance moduleV freeV inferInstance finiteV d hd
  let e : (Fin d → ZMod p) ≃ₗ[ZMod p] V := b.equivFun.symm
  exact ⟨AddEquiv.toMultiplicativeLeft e.toAddEquiv⟩

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.PrimeTorsionLabels
