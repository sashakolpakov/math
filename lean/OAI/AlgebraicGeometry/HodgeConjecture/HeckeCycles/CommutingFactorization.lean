import Mathlib

/-! # Commuting Factorization -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.CommutingFactorization.CM

noncomputable section

/-! An actual homomorphism factors through an active group and the
range of its commuting remainder, with exact rational recovery. -/

variable {G A M : Type*} [Group G] [Group A] [Group M]
  (a : G →* A) (active : A →* M) (rho : G →* M)

def remainder (g : G) : M := (active (a g))⁻¹ * rho g

theorem factorization (g : G) : active (a g) * remainder a active rho g = rho g := by
  simp only [remainder, ← mul_assoc, mul_inv_cancel, one_mul]

variable (hc : ∀ g u, Commute (remainder a active rho g) (active u))

include hc in
theorem remainder_mul (g h : G) :
    remainder a active rho (g * h) = remainder a active rho g * remainder a active rho h := by
  apply mul_left_cancel (a := active (a (g * h)))
  rw [factorization, map_mul, map_mul, map_mul]
  rw [← factorization a active rho g, ← factorization a active rho h]
  exact (hc g (a h)).mul_mul_mul_comm _ _

def awayHom : G →* M where
  toFun := remainder a active rho
  map_one' := by simp [remainder]
  map_mul' := remainder_mul a active rho hc

abbrev Away := (awayHom a active rho hc).range

def away : G →* Away a active rho hc := (awayHom a active rho hc).rangeRestrict

theorem away_commutes (b : Away a active rho hc) (u : A) : Commute b.val (active u) := by
  obtain ⟨g, hg⟩ := b.property
  exact hg ▸ hc g u

def splitting : A × Away a active rho hc →* M where
  toFun p := active p.1 * p.2.val
  map_one' := by change active 1 * 1 = 1; rw [map_one, one_mul]
  map_mul' p q := by
    change active (p.1 * q.1) * (p.2.val * q.2.val) =
      (active p.1 * p.2.val) * (active q.1 * q.2.val)
    rw [map_mul]
    exact ((away_commutes a active rho hc p.2 q.1).mul_mul_mul_comm _ _).symm

theorem rational_recovery (g : G) :
    splitting a active rho hc (a g, away a active rho hc g) = rho g :=
  factorization a active rho g

variable {B : Type*} [Group B] (b : G →* B)

def coordinateHom : G →* B × M := b.prod (awayHom a active rho hc)

abbrev AwayWithCoordinates := (coordinateHom a active rho hc b).range

def awayWithCoordinates : G →* AwayWithCoordinates a active rho hc b :=
  (coordinateHom a active rho hc b).rangeRestrict

theorem coordinate_commutes (v : AwayWithCoordinates a active rho hc b) (u : A) :
    Commute v.val.2 (active u) := by
  obtain ⟨g, hg⟩ := v.property
  exact (congrArg Prod.snd hg) ▸ hc g u

local instance coordinateMulOneClass : MulOneClass (AwayWithCoordinates a active rho hc b) :=
  (Subgroup.toGroup (AwayWithCoordinates a active rho hc b)).toMulOneClass

def coordinateSplitting : A × AwayWithCoordinates a active rho hc b →* M where
  toFun p := active p.1 * p.2.val.2
  map_one' := by change active 1 * 1 = 1; rw [map_one, one_mul]
  map_mul' p q := by
    change active (p.1 * q.1) * (p.2.val.2 * q.2.val.2) =
      (active p.1 * p.2.val.2) * (active q.1 * q.2.val.2)
    rw [map_mul]
    exact ((coordinate_commutes a active rho hc b p.2 q.1).mul_mul_mul_comm _ _).symm

theorem coordinate_recovery (g : G) :
    coordinateSplitting a active rho hc b (a g, awayWithCoordinates a active rho hc b g) = rho g :=
  factorization a active rho g

theorem away_coordinates (g : G) : (awayWithCoordinates a active rho hc b g).val.1 = b g := rfl

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.CommutingFactorization.CM
