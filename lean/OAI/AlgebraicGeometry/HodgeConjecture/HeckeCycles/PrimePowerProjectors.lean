import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ProjectorRangeFree
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.RingTheory.LocalRing.RingHom.Basic

/-! # Prime Power Projectors -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.PrimePowerProjectors.CM

noncomputable section

/-! Coefficient projectors on standard q-power torsion coordinates have
finite free ranges over the actual residue ring Z/q^n. -/

variable (q : ℕ) [Fact q.Prime]

theorem residue_isLocalRing (n : ℕ) : IsLocalRing (ZMod (q ^ (n + 1))) := by
  let : Fact (1 < q ^ (n + 1)) := ⟨one_lt_pow' (Fact.out : q.Prime).one_lt (Nat.succ_ne_zero n)⟩
  exact IsLocalRing.of_surjective (PadicInt.toZModPow (p := q) (n + 1))
    (ZMod.ringHom_surjective _)

theorem projector_range_free (n g : ℕ)
    (p : Module.End (ZMod (q ^ (n + 1))) (Fin g → ZMod (q ^ (n + 1))))
    (hp : p * p = p) : Module.Free (ZMod (q ^ (n + 1))) p.range := by
  let : IsLocalRing (ZMod (q ^ (n + 1))) := residue_isLocalRing q n
  exact ProjectorRangeFree.CM.range_free p hp

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.PrimePowerProjectors.CM
