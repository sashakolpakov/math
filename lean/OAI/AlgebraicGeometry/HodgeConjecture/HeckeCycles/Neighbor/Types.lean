import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.HeckeExponents
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.IsogenyQuotientFibers

/-! # Types -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Neighbor.Types.CM

noncomputable section

/-! The three native NeighborCounting elementary types define genuine integral
TateComparison cocharacters, with exactly the same common multiplier and every
chosen-side exponent. -/

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.HeckeExponents

variable {s : ℕ} (active : Fin s) (multiplicative : Fin s → Bool)

theorem exponents_antitone (i : Fin 3) (v : Fin s) :
    Antitone (Isogenies.NeighborCounting.HeckeExponents.neighborExponents active multiplicative i v) := by
  intro a b hab
  have hab' : a.val ≤ b.val := hab
  unfold Isogenies.NeighborCounting.HeckeExponents.neighborExponents Isogenies.NeighborCounting.HeckeExponents.activeExponents
  split_ifs <;> omega

def localType (i : Fin 3) : AbelianScheme.TateComparison.Local.LocalType s where
  multiplier := Isogenies.NeighborCounting.HeckeExponents.neighborLevel i
  exponent v k := Isogenies.NeighborCounting.HeckeExponents.neighborExponents active multiplicative i v k
  dominant v _ _ hab := Int.ofNat_le.mpr (exponents_antitone active multiplicative i v hab)

theorem isIntegral (i : Fin 3) : (localType active multiplicative i).IsIntegral :=
  ⟨Int.natCast_nonneg _, fun v k => ⟨Int.natCast_nonneg _,
    Int.ofNat_le.mpr (Isogenies.NeighborCounting.HeckeExponents.neighborExponents_bound active multiplicative i v k)⟩⟩

def integralType (i : Fin 3) : AbelianScheme.TateComparison.Local.IntegralType s :=
  ⟨localType active multiplicative i, isIntegral active multiplicative i⟩

theorem multiplier (i : Fin 3) :
    (integralType active multiplicative i).multiplierNat = Isogenies.NeighborCounting.HeckeExponents.neighborLevel i := Int.toNat_natCast _

theorem exponents (i : Fin 3) :
    (integralType active multiplicative i).exponentNat = Isogenies.NeighborCounting.HeckeExponents.neighborExponents active multiplicative i := by
  funext v k
  exact Int.toNat_natCast _

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Neighbor.Types.CM
