import OAI.NumberTheory.ArithmeticGroups.Lattices.Split.SiegelFiniteVolume
import OAI.NumberTheory.ArithmeticGroups.Lattices.CompactFactorFiniteVolume
import OAI.NumberTheory.ArithmeticGroups.Lattices.Compact.FilteredProductCoordinates

/-! # Intrinsic Siegel Finite Volume -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices

noncomputable section

section

/-! Intrinsic compact/split/unipotent Siegel sets have finite right
Haar volume in an adjoint-stable semisimple bracket automorphism group. -/

open _root_.MeasureTheory _root_.MeasureTheory.Measure _root_.ContinuousLinearMap
open scoped Pointwise

variable {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℝ L] [FiniteDimensional ℝ L]
  {B : L →L[ℝ] L →L[ℝ] L}

local instance IntrinsicSiegelFiniteVolume.Construction.intrinsicSiegel_complete : CompleteSpace L := FiniteDimensional.complete ℝ L
local instance IntrinsicSiegelFiniteVolume.Construction.intrinsicSiegelEnd_normed : NormedAddCommGroup (L →L[ℝ] L) := inferInstance
local instance IntrinsicSiegelFiniteVolume.Construction.intrinsicSiegelEnd_space : NormedSpace ℝ (L →L[ℝ] L) := inferInstance
local instance IntrinsicSiegelFiniteVolume.Construction.intrinsicSiegelEnd_finite : FiniteDimensional ℝ (L →L[ℝ] L) := inferInstance

def KillingSplit.Construction.KillingSplitWeightData.intrinsicSiegelSet (d : KillingSplit.Construction.KillingSplitWeightData B) (t : ℝ)
    (S : Set (UnipotentBracketGroup.Construction.unipotentBracketUnitGroup B d.basis (fun i => d.weight i d.regularElement))) :
    Set (UnipotentBracketGroup.Construction.continuousBracketUnitGroup B) :=
  Set.range (Subgroup.inclusion (show OrthogonalBracketUnitCompactness.Construction.orthogonalBracketUnitGroup B ≤ UnipotentBracketGroup.Construction.continuousBracketUnitGroup B
    from fun _ hg => hg.1)) *
  (Subgroup.inclusion (show Split.FilteredBracketGroup.Construction.splitFilteredBracketUnitGroup B d.basis.toBasis
    (fun i => d.weight i d.regularElement) d.subspace d.commute ≤ UnipotentBracketGroup.Construction.continuousBracketUnitGroup B
    from fun _ hg => hg.1) '' d.splitSiegelSet t S)

theorem KillingSplit.Construction.KillingSplitWeightData.intrinsicSiegelSet_inverseHaar_lt_top
    [MeasurableSpace (L →L[ℝ] L)ˣ] [BorelSpace (L →L[ℝ] L)ˣ]
    (d : KillingSplit.Construction.KillingSplitWeightData B) (hB : ContinuousBracketConstraints.Construction.IsContinuousLieBracket B)
    (hK : (ContinuousInnerDerivations.Construction.continuousBracketKillingForm B).Nondegenerate)
    (hadj : ∀ g : L ≃L[ℝ] L, ContinuousBracketChange.Construction.continuousBracketChange g B = B →
      ∀ x y, adjoint g.toContinuousLinearMap (B x y) =
        B (adjoint g.toContinuousLinearMap x) (adjoint g.toContinuousLinearMap y))
    (hDadj : ∀ X, Lie.AutomorphismTransversal.Construction.continuousBilinearDerivationDefect B X = 0 →
      Lie.AutomorphismTransversal.Construction.continuousBilinearDerivationDefect B (adjoint X) = 0)
    (μ : Measure (UnipotentBracketGroup.Construction.continuousBracketUnitGroup B)) [IsHaarMeasure μ]
    (t : ℝ) (ht : 0 ≤ t)
    (S : Set (UnipotentBracketGroup.Construction.unipotentBracketUnitGroup B d.basis (fun i => d.weight i d.regularElement)))
    (hS : IsCompact S) : μ.inv (d.intrinsicSiegelSet t S) < ⊤ := by
  let : MeasurableSpace (L →L[ℝ] L) := borel _
  let : BorelSpace (L →L[ℝ] L) := ⟨rfl⟩
  let : LocallyCompactSpace (L →L[ℝ] L)ˣ := Units.isOpenEmbedding_val.locallyCompactSpace
  let : SecondCountableTopology (L →L[ℝ] L)ˣ := Units.isOpenEmbedding_val.isEmbedding.secondCountableTopology
  let P := Split.FilteredBracketGroup.Construction.splitFilteredBracketUnitGroup B d.basis.toBasis (fun i => d.weight i d.regularElement)
    d.subspace d.commute
  have hP : IsClosed (P : Set (L →L[ℝ] L)ˣ) :=
    Split.FilteredBracketGroup.Construction.splitFilteredBracketUnitGroup_isClosed B d.basis.toBasis (fun i => d.weight i d.regularElement)
      d.subspace (fun _ hA => (d.le_symmetric hA).1) d.commute
  let : LocallyCompactSpace P := hP.isClosedEmbedding_subtypeVal.locallyCompactSpace
  let ν := haar (G := P)
  apply CompactFactorFiniteVolume.Construction.relative_compact_factor_inverseHaar_lt_top (UnipotentBracketGroup.Construction.continuousBracketUnitGroup B)
    (OrthogonalBracketUnitCompactness.Construction.orthogonalBracketUnitGroup B) P (UnipotentBracketGroup.Construction.continuousBracketUnitGroup_isClosed B)
    (OrthogonalBracketUnitCompactness.Construction.orthogonalBracketUnitGroup_isCompact B) hP (fun _ hg => hg.1) (fun _ hg => hg.1)
    (Compact.SplitFilteredDisjoint.Construction.orthogonal_splitFiltered_inf_eq_bot B d.basis (fun i => d.weight i d.regularElement)
      d.subspace (fun _ hA => (d.le_symmetric hA).1) d.commute) _ μ ν
  · exact d.splitSiegelSet_inverseHaar_lt_top hB hK ν t ht S hS
  · intro g hg
    exact GlobalSplitFilteredProduct.Construction.bracket_global_splitFiltered_product B hadj d.subspace d.regularElement.val d.le_symmetric d.commute
      d.regularElement.property (d.linear_iwasawa hDadj) d.basis (fun i => d.weight i d.regularElement)
      (fun i => d.eigenvector i d.regularElement) g hg

end

/-! Membership in an intrinsic Siegel set expressed through its
compact, split, and unipotent factors. -/

open scoped Pointwise

theorem KillingSplit.Construction.KillingSplitWeightData.mem_intrinsicSiegelSet_of_factors
    {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℝ L] [FiniteDimensional ℝ L]
    {B : L →L[ℝ] L →L[ℝ] L} (d : KillingSplit.Construction.KillingSplitWeightData B) (t : ℝ)
    (S : Set (UnipotentBracketGroup.Construction.unipotentBracketUnitGroup B d.basis (fun i => d.weight i d.regularElement)))
    (g : UnipotentBracketGroup.Construction.continuousBracketUnitGroup B) (k : OrthogonalBracketUnitCompactness.Construction.orthogonalBracketUnitGroup B)
    (A : d.subspace) (hA : A ∈ d.truncatedNegativeChamber t)
    (n : UnipotentBracketGroup.Construction.unipotentBracketUnitGroup B d.basis (fun i => d.weight i d.regularElement))
    (hn : n ∈ S) (he : g.val = k.val * OperatorExponentialUnits.Construction.operatorExpUnit A.val * n.val) :
    g ∈ d.intrinsicSiegelSet t S := by
  let ik := Subgroup.inclusion (show OrthogonalBracketUnitCompactness.Construction.orthogonalBracketUnitGroup B ≤ UnipotentBracketGroup.Construction.continuousBracketUnitGroup B
    from fun _ hk => hk.1)
  let ip := Subgroup.inclusion (show Split.FilteredBracketGroup.Construction.splitFilteredBracketUnitGroup B d.basis.toBasis
    (fun i => d.weight i d.regularElement) d.subspace d.commute ≤ UnipotentBracketGroup.Construction.continuousBracketUnitGroup B
    from fun _ hp => hp.1)
  let p := d.additiveSplitProductHomeomorph (Multiplicative.ofAdd A, n)
  have hp : p ∈ d.splitSiegelSet t S := ⟨(Multiplicative.ofAdd A, n), ⟨hA, hn⟩, rfl⟩
  refine Set.mem_mul.mpr ⟨ik k, ⟨k, rfl⟩, ip p, ⟨p, hp, rfl⟩, ?_⟩
  apply Subtype.ext
  change k.val * (OperatorExponentialUnits.Construction.operatorExpUnit A.val * n.val) = g.val
  rw [← mul_assoc, ← he]

end

end OAI.NumberTheory.ArithmeticGroups.Lattices
