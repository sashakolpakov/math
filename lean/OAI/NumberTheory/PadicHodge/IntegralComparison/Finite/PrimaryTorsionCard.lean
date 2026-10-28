import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Add
import Mathlib.GroupTheory.Sylow

/-! # Primary Torsion Card -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Finite.PrimaryTorsionCard

noncomputable section

/-! The full prime-primary subgroup of a finite abelian group has the
prime-primary part of its cardinality. -/

open OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Add

variable (p : ℕ) [Fact p.Prime] (G : Type*) [AddCommGroup G] [Finite G]

theorem card_torsion :
    Nat.card (AlgebraicGeometry.AbelianScheme.TateComparison.Add.Tate.torsion p G ((Nat.card G).factorization p)) =
      p ^ (Nat.card G).factorization p := by
  let N := (AlgebraicGeometry.AbelianScheme.TateComparison.Add.Tate.torsion p G ((Nat.card G).factorization p)).toSubgroup
  let P : Sylow p (Multiplicative G) := Classical.arbitrary _
  have hN : IsPGroup p N := by
    intro x
    refine ⟨(Nat.card G).factorization p, Subtype.ext ?_⟩
    exact x.property
  have hNP : N ≤ P := hN.le_sylow_of_normal P
  have hPN : (P : Subgroup (Multiplicative G)) ≤ N := by
    intro x hx
    have he := congrArg Subtype.val (pow_card_eq_one' (x := (⟨x, hx⟩ : P)))
    change x ^ Nat.card (P : Subgroup (Multiplicative G)) = 1 at he
    rw [P.card_eq_multiplicity] at he
    exact he
  have he : N = (P : Subgroup (Multiplicative G)) := le_antisymm hNP hPN
  have hc : Nat.card N = Nat.card P := congrArg (fun S : Subgroup (Multiplicative G) =>
    Nat.card S) he
  exact hc.trans P.card_eq_multiplicity

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Finite.PrimaryTorsionCard
