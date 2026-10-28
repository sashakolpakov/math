import OAI.NumberTheory.ArithmeticGroups.Lattices.SpectralOperatorExponential
import OAI.NumberTheory.ArithmeticGroups.Lattices.ProperMapNormBound
import OAI.NumberTheory.ArithmeticGroups.Lattices.OperatorExponentialUnits

/-! # Commuting Exponential Subgroup -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.CommutingExponentialSubgroup.Construction

noncomputable section

section

/-! Exponentiation on a subspace of symmetric operators is proper
as a map to the invertible operators, and therefore has closed image. -/

open NormedSpace

variable {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℝ L] [FiniteDimensional ℝ L]

theorem symmetric_subspace_exponential_isProperMap
    (a : Submodule ℝ (L →L[ℝ] L)) (ha : ∀ X ∈ a, X.toLinearMap.IsSymmetric) :
    IsProperMap (fun X : a => OperatorExponentialUnits.Construction.operatorExpUnit X.val) := by
  let : CompleteSpace L := FiniteDimensional.complete ℝ L
  let : ProperSpace a := FiniteDimensional.proper ℝ a
  let : FirstCountableTopology (L →L[ℝ] L)ˣ := Units.isInducing_embedProduct.firstCountableTopology
  let h : (L →L[ℝ] L)ˣ → ℝ := fun g => Module.finrank ℝ L *
    (‖(g : L →L[ℝ] L)‖ + ‖(↑g⁻¹ : L →L[ℝ] L)‖)
  have hh : Continuous h := continuous_const.mul
    (Units.continuous_val.norm.add Units.continuous_coe_inv.norm)
  apply ProperMapNormBound.Construction.isProperMap_of_continuous_norm_bound (fun X : a => OperatorExponentialUnits.Construction.operatorExpUnit X.val)
    (OperatorExponentialUnits.Construction.operatorExpUnit_continuous.comp continuous_subtype_val) h hh
  intro X
  exact SpectralOperatorExponential.Construction.symmetric_norm_le_exponentials X.val (ha X.val X.property)

theorem symmetric_subspace_exponential_isClosed
    (a : Submodule ℝ (L →L[ℝ] L)) (ha : ∀ X ∈ a, X.toLinearMap.IsSymmetric) :
    IsClosed (Set.range (fun X : a => OperatorExponentialUnits.Construction.operatorExpUnit X.val)) :=
  (symmetric_subspace_exponential_isProperMap a ha).isClosed_range

end

/-! A commuting symmetric subspace exponentiates to a closed subgroup. -/

variable {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℝ L] [FiniteDimensional ℝ L]

def commutingExponentialHom (a : Submodule ℝ (L →L[ℝ] L))
    (hc : ∀ X ∈ a, ∀ Y ∈ a, Commute X Y) : Multiplicative a →* (L →L[ℝ] L)ˣ where
  toFun X := OperatorExponentialUnits.Construction.operatorExpUnit X.toAdd.val
  map_one' := OperatorExponentialUnits.Construction.operatorExpUnit_zero
  map_mul' X Y := OperatorExponentialUnits.Construction.operatorExpUnit_add X.toAdd.val Y.toAdd.val
    (hc X.toAdd.val X.toAdd.property Y.toAdd.val Y.toAdd.property)

def commutingExponentialSubgroup (a : Submodule ℝ (L →L[ℝ] L))
    (hc : ∀ X ∈ a, ∀ Y ∈ a, Commute X Y) : Subgroup (L →L[ℝ] L)ˣ :=
  (commutingExponentialHom a hc).range

theorem commutingExponentialSubgroup_isClosed (a : Submodule ℝ (L →L[ℝ] L))
    (ha : ∀ X ∈ a, X.toLinearMap.IsSymmetric)
    (hc : ∀ X ∈ a, ∀ Y ∈ a, Commute X Y) :
    IsClosed (commutingExponentialSubgroup a hc : Set (L →L[ℝ] L)ˣ) := by
  change IsClosed (Set.range (fun X : a => OperatorExponentialUnits.Construction.operatorExpUnit X.val))
  exact symmetric_subspace_exponential_isClosed a ha

theorem commutingExponentialSubgroup_le_bracket
    (B : L →L[ℝ] L →L[ℝ] L) (a : Submodule ℝ (L →L[ℝ] L))
    (ha : a ≤ RegularSymmetricDerivation.Construction.symmetricDerivationSubmodule B) (hc : ∀ X ∈ a, ∀ Y ∈ a, Commute X Y) :
    commutingExponentialSubgroup a hc ≤ UnipotentBracketGroup.Construction.continuousBracketUnitGroup B := by
  rintro g ⟨X, rfl⟩
  exact Bilinear.DerivationExponential.Construction.exp_bilinear_derivation_preserves B X.toAdd.val
    ((OrthogonalBracketAlgebra.Construction.continuousBilinearDerivationDefect_eq_zero_iff B _).mp (ha X.toAdd.property).2)

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.CommutingExponentialSubgroup.Construction
