import OAI.NumberTheory.ArithmeticGroups.Lattices.ContinuousBracketConstraints
import OAI.NumberTheory.ArithmeticGroups.Lattices.Lie.JacobiTangent
import Mathlib.Algebra.Lie.Derivation.Killing

/-! # Continuous Inner Derivations -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.ContinuousInnerDerivations.Construction

noncomputable section

section

/-! The continuous bracket equations have exactly the change-of-basis
tangent directions when the Killing form is nondegenerate. -/

open LieModule.Cohomology

variable {L : Type*} [NormedAddCommGroup L] [NormedSpace ℝ L] [FiniteDimensional ℝ L]

local instance killingEnd_normed : NormedAddCommGroup (L →L[ℝ] L) := inferInstance
local instance killingEnd_space : NormedSpace ℝ (L →L[ℝ] L) := inferInstance
local instance killingBilinear_normed : NormedAddCommGroup (L →L[ℝ] L →L[ℝ] L) := inferInstance
local instance killingBilinear_space : NormedSpace ℝ (L →L[ℝ] L →L[ℝ] L) := inferInstance

@[instance_reducible]
def continuousBracketLieRing (B : L →L[ℝ] L →L[ℝ] L) (hB : ContinuousBracketConstraints.Construction.IsContinuousLieBracket B) : LieRing L where
  toAddCommGroup := inferInstance
  bracket x y := B x y
  add_lie x y z := by simp only [map_add, add_apply]
  lie_add x y z := (B x).map_add y z
  lie_self := hB.1
  leibniz_lie x y z := ((ContinuousJacobi.Construction.continuousJacobi_zero_iff B).mp hB.2 x y z).trans (add_comm _ _)

@[instance_reducible]
def continuousBracketLieAlgebra (B : L →L[ℝ] L →L[ℝ] L) (hB : ContinuousBracketConstraints.Construction.IsContinuousLieBracket B) :
    @LieAlgebra ℝ L _ (continuousBracketLieRing B hB) := by
  let : LieRing L := continuousBracketLieRing B hB
  exact { toModule := inferInstance, lie_smul := fun c x y => (B x).map_smul c y }

def continuousBracketKillingForm (B : L →L[ℝ] L →L[ℝ] L) : LinearMap.BilinForm ℝ L :=
  ((LinearMap.mul ℝ (Module.End ℝ L)).compl₁₂ (ContinuousBracketChange.Construction.finiteBilinearEquiv.symm B)
    (ContinuousBracketChange.Construction.finiteBilinearEquiv.symm B)).compr₂ (LinearMap.trace ℝ L)

theorem continuousBracketKillingForm_apply (B : L →L[ℝ] L →L[ℝ] L) (x y : L) :
    continuousBracketKillingForm B x y = LinearMap.trace ℝ L
      ((B x).toLinearMap * (B y).toLinearMap) := rfl

attribute [local instance] LieRing.ofAssociativeRing

theorem continuousBracketLinearization_kernel
    (B : L →L[ℝ] L →L[ℝ] L) (hB : ContinuousBracketConstraints.Construction.IsContinuousLieBracket B)
    (hK : (continuousBracketKillingForm B).Nondegenerate) :
    (ContinuousBracketConstraints.Construction.continuousBracketLinearization B).toLinearMap.ker =
      (Lattices.Lie.AutomorphismTransversal.Construction.continuousBilinearDerivationDefect B).toLinearMap.range := by
  let : LieRing L := continuousBracketLieRing B hB
  let : LieAlgebra ℝ L := continuousBracketLieAlgebra B hB
  have had : ContinuousBracketChange.Construction.finiteBilinearEquiv.symm B = (LieAlgebra.ad ℝ L).toLinearMap := by
    ext x y
    rfl
  have hform : killingForm ℝ L = continuousBracketKillingForm B := by
    ext x y
    rfl
  have hdef (T : L →L[ℝ] L) :
      ContinuousBracketChange.Construction.finiteBilinearEquiv.symm (Lattices.Lie.AutomorphismTransversal.Construction.continuousBilinearDerivationDefect B T) =
        Lattices.Lie.DerivationDefect.Construction.lieDerivationDefect ℝ L T.toLinearMap := by
    ext x y
    rfl
  apply le_antisymm
  · intro C hC
    obtain ⟨hAlt, hJac⟩ := (ContinuousBracketConstraints.Construction.continuousBracketLinearization_eq_zero B C).mp hC
    have hJac' : JacobiLinearization.Construction.jacobiLinearization (LieAlgebra.ad ℝ L).toLinearMap
        (ContinuousBracketChange.Construction.finiteBilinearEquiv.symm C) = 0 := by
      apply ContinuousBracketChange.Construction.finiteTrilinearEquiv.injective
      rw [map_zero, ← had, ← ContinuousJacobi.Construction.continuousJacobiLinearization_eq_algebraic]
      exact hJac
    obtain ⟨T, hT⟩ := Lattices.Lie.JacobiTangent.Construction.killing_jacobi_tangent_is_derivationDefect
      (hform.symm ▸ hK) (ContinuousBracketChange.Construction.finiteBilinearEquiv.symm C) hAlt hJac'
    refine ⟨T.toContinuousLinearMap, ?_⟩
    apply ContinuousBracketChange.Construction.finiteBilinearEquiv.symm.injective
    exact (hdef T.toContinuousLinearMap).trans hT
  · rintro _ ⟨T, rfl⟩
    change ContinuousBracketConstraints.Construction.continuousBracketLinearization B (Lattices.Lie.AutomorphismTransversal.Construction.continuousBilinearDerivationDefect B T) = 0
    apply (ContinuousBracketConstraints.Construction.continuousBracketLinearization_eq_zero B _).mpr
    constructor
    · intro x
      have he := congrArg (fun C : L →ₗ[ℝ] L →ₗ[ℝ] L => C x x)
        (Lattices.Lie.JacobiTangent.Construction.lieDerivationDefect_eq_negative_coboundary T.toLinearMap)
      exact he.trans ((d₁₂ ℝ L L (-T.toLinearMap)).property x)
    · rw [ContinuousJacobi.Construction.continuousJacobiLinearization_eq_algebraic, had, hdef,
        Lattices.Lie.JacobiTangent.Construction.lieDerivationDefect_jacobiLinearization, map_zero]

end

/-! The adjoint map of a nondegenerate Killing bracket is injective,
and its image consists of all continuous derivations. -/

variable {L : Type*} [NormedAddCommGroup L] [NormedSpace ℝ L] [FiniteDimensional ℝ L]

theorem continuousKillingBracket_injective
    (B : L →L[ℝ] L →L[ℝ] L) (hK : (continuousBracketKillingForm B).Nondegenerate) :
    Function.Injective B := by
  apply (injective_iff_map_eq_zero B).mpr
  intro x hx
  apply hK.1 x
  intro y
  rw [continuousBracketKillingForm_apply, hx]
  change LinearMap.trace ℝ L (0 * (B y).toLinearMap) = 0
  rw [zero_mul, map_zero]

attribute [local instance] LieRing.ofAssociativeRing

theorem continuousKillingBracket_derivation_kernel
    (B : L →L[ℝ] L →L[ℝ] L) (hB : ContinuousBracketConstraints.Construction.IsContinuousLieBracket B)
    (hK : (continuousBracketKillingForm B).Nondegenerate) :
    (Lattices.Lie.AutomorphismTransversal.Construction.continuousBilinearDerivationDefect B).toLinearMap.ker = B.toLinearMap.range := by
  let : LieRing L := continuousBracketLieRing B hB
  let : LieAlgebra ℝ L := continuousBracketLieAlgebra B hB
  have hform : killingForm ℝ L = continuousBracketKillingForm B := by ext x y; rfl
  let : LieAlgebra.IsKilling ℝ L := by
    constructor
    apply le_antisymm _ bot_le
    intro x hx
    change x = 0
    exact (hform.symm ▸ hK).2 x (fun y => hx y (LieSubmodule.mem_top y))
  apply le_antisymm
  · intro T hT
    have hd : Lattices.Lie.DerivationDefect.Construction.lieDerivationDefect ℝ L T.toLinearMap = 0 := by
      apply LinearMap.ext
      intro x
      apply LinearMap.ext
      intro y
      exact congrArg (fun C : L →L[ℝ] L →L[ℝ] L => C x y) hT
    obtain ⟨D, hD⟩ := (Lattices.Lie.DerivationDefect.Construction.lieDerivationDefect_eq_zero_iff T.toLinearMap).mp hd
    obtain ⟨x, hx⟩ := LieDerivation.IsKilling.exists_eq_ad D
    refine ⟨x, ?_⟩
    apply ContinuousLinearMap.ext
    intro y
    have he := congrArg LieDerivation.toLinearMap hx
    rw [LieDerivation.coe_ad_apply_eq_ad_apply, hD] at he
    exact DFunLike.congr_fun he y
  · rintro _ ⟨x, rfl⟩
    apply ContinuousLinearMap.ext
    intro y
    apply ContinuousLinearMap.ext
    intro z
    exact congrArg (fun C : L →ₗ[ℝ] L →ₗ[ℝ] L => C y z)
      (Lattices.Lie.DerivationDefect.Construction.lieDerivationDefect_ad (R := ℝ) (L := L) x)

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.ContinuousInnerDerivations.Construction
