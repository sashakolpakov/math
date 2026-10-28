import OAI.NumberTheory.ArithmeticGroups.Lattices.OperatorExponentialUnits
import OAI.NumberTheory.ArithmeticGroups.Lattices.OrthogonalBracketUnitCompactness
import OAI.NumberTheory.ArithmeticGroups.Lattices.Bracket.CartanDecomposition
import Mathlib.Topology.Connected.Clopen

/-! # Exponential Component -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.Bracket.ExponentialComponent.Construction

noncomputable section

/-! Exponentials of derivations lie in the identity component, and
Cartan decomposition puts every automorphism in a compact factor times that component. -/

open scoped _root_.Topology
open _root_.ContinuousLinearMap Set

variable {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℝ L] [FiniteDimensional ℝ L]

theorem bracket_exponential_mem_connectedComponent
    (B : L →L[ℝ] L →L[ℝ] L) (D : L →L[ℝ] L)
    (hD : Lie.AutomorphismTransversal.Construction.continuousBilinearDerivationDefect B D = 0)
    (g : UnipotentBracketGroup.Construction.continuousBracketUnitGroup B) (hg : g.val = OperatorExponentialUnits.Construction.operatorExpUnit D) :
    g ∈ connectedComponent (1 : UnipotentBracketGroup.Construction.continuousBracketUnitGroup B) := by
  let : CompleteSpace L := FiniteDimensional.complete ℝ L
  have hd (t : ℝ) : Lie.AutomorphismTransversal.Construction.continuousBilinearDerivationDefect B (t • D) = 0 := by
    rw [map_smul, hD]
    ext x y
    exact smul_zero t
  let f : ℝ → UnipotentBracketGroup.Construction.continuousBracketUnitGroup B := fun t =>
    ⟨OperatorExponentialUnits.Construction.operatorExpUnit (t • D), Bilinear.DerivationExponential.Construction.exp_bilinear_derivation_preserves B (t • D)
      ((OrthogonalBracketAlgebra.Construction.continuousBilinearDerivationDefect_eq_zero_iff B _).mp (hd t))⟩
  have hf : Continuous f :=
    (OperatorExponentialUnits.Construction.operatorExpUnit_continuous.comp (continuous_id.smul continuous_const)).subtype_mk _
  have hf0 : f 0 = 1 := by
    apply Subtype.ext
    change OperatorExponentialUnits.Construction.operatorExpUnit ((0 : ℝ) • D) = 1
    rw [zero_smul, OperatorExponentialUnits.Construction.operatorExpUnit_zero]
  have hf1 : f 1 = g := by
    apply Subtype.ext
    change OperatorExponentialUnits.Construction.operatorExpUnit ((1 : ℝ) • D) = g.val
    rw [one_smul, hg]
  have hsub : Set.range f ⊆ connectedComponent (1 : UnipotentBracketGroup.Construction.continuousBracketUnitGroup B) :=
    (isPreconnected_range hf).subset_connectedComponent ⟨0, hf0⟩
  exact hsub ⟨1, hf1⟩

theorem bracket_automorphism_compact_component
    (B : L →L[ℝ] L →L[ℝ] L)
    (hadj : ∀ g : L ≃L[ℝ] L, ContinuousBracketChange.Construction.continuousBracketChange g B = B →
      ∀ x y, adjoint g.toContinuousLinearMap (B x y) =
        B (adjoint g.toContinuousLinearMap x) (adjoint g.toContinuousLinearMap y))
    (g : (L →L[ℝ] L)ˣ) (hg : g ∈ UnipotentBracketGroup.Construction.continuousBracketUnitGroup B) :
    ∃ k ∈ OrthogonalBracketUnitCompactness.Construction.orthogonalBracketUnitGroup B, ∃ h : UnipotentBracketGroup.Construction.continuousBracketUnitGroup B,
      h ∈ connectedComponent (1 : UnipotentBracketGroup.Construction.continuousBracketUnitGroup B) ∧ g = k * h.val := by
  let : CompleteSpace L := FiniteDimensional.complete ℝ L
  let e := ContinuousLinearEquiv.ofUnit g
  have he : ContinuousBracketChange.Construction.continuousBracketChange e B = B := (PolarDecomposition.Construction.continuousBracketChange_eq_self_iff B e).mpr hg
  obtain ⟨k, D, hkB, hkI, _, hD, hprod⟩ := CartanDecomposition.Construction.bracket_automorphism_cartan_decomposition B e he (hadj e he)
  have hDu : OperatorExponentialUnits.Construction.operatorExpUnit D ∈ UnipotentBracketGroup.Construction.continuousBracketUnitGroup B :=
    Bilinear.DerivationExponential.Construction.exp_bilinear_derivation_preserves B D ((OrthogonalBracketAlgebra.Construction.continuousBilinearDerivationDefect_eq_zero_iff B D).mp hD)
  let h : UnipotentBracketGroup.Construction.continuousBracketUnitGroup B := ⟨OperatorExponentialUnits.Construction.operatorExpUnit D, hDu⟩
  refine ⟨k.toUnit, ⟨(PolarDecomposition.Construction.continuousBracketChange_eq_self_iff B k).mp hkB, hkI⟩, h,
    bracket_exponential_mem_connectedComponent B D hD h rfl, ?_⟩
  apply Units.ext
  exact hprod

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.Bracket.ExponentialComponent.Construction
