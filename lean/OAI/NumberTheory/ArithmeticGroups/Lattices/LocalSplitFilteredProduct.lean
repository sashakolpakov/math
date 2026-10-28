import OAI.NumberTheory.ArithmeticGroups.Lattices.Split.FilteredFactorInclusions
import OAI.NumberTheory.ArithmeticGroups.Lattices.LocalIwasawaProduct
import OAI.NumberTheory.ArithmeticGroups.Lattices.Bracket.SubgroupLocalProduct

/-! # Local Split Filtered Product -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.LocalSplitFilteredProduct.Construction

noncomputable section

/-! Local Iwasawa factors lie in a compact subgroup times a closed
filtered subgroup; this product contains the identity component. -/

open scoped Classical _root_.Topology Pointwise _root_.Matrix.Norms.Operator
open NormedSpace Filter Set

variable {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℝ L] [FiniteDimensional ℝ L]

theorem bracket_local_splitFiltered_product {m : ℕ}
    (B : L →L[ℝ] L →L[ℝ] L) (a : Submodule ℝ (L →L[ℝ] L)) (H : L →L[ℝ] L)
    (ha : a ≤ RegularSymmetricDerivation.Construction.symmetricDerivationSubmodule B) (hc : ∀ X ∈ a, ∀ Y ∈ a, Commute X Y) (hH : H ∈ a)
    (hsum : DerivationSpectralDecomposition.Construction.bracketDerivationSubmodule B = DerivationSpectralDecomposition.Construction.skewBracketDerivations B ⊔ a ⊔ DerivationSpectralDecomposition.Construction.positiveBracketDerivations B H)
    (b : OrthonormalBasis (Fin m) ℝ L) (w : Fin m → ℝ) (heig : ∀ i, H (b i) = w i • b i) :
    ∀ᶠ T in 𝓝 (1 : L →L[ℝ] L),
      (∀ x y, T (B x y) = B (T x) (T y)) →
      ∃ k ∈ OrthogonalBracketUnitCompactness.Construction.orthogonalBracketUnitGroup B, ∃ p ∈ Split.FilteredBracketGroup.Construction.splitFilteredBracketUnitGroup B b.toBasis w a hc,
        (k : L →L[ℝ] L) * (p : L →L[ℝ] L) = T := by
  let : CompleteSpace L := FiniteDimensional.complete ℝ L
  have h := LocalIwasawaProduct.Construction.bracket_local_iwasawa_product B a H ha hH hsum b w heig
  filter_upwards [h] with T hT
  intro hTB
  obtain ⟨k, hk, A, hA, n, hn, he⟩ := hT hTB
  let u := (OrthogonalBracketAlgebra.Construction.orthogonalBracketEquiv B k hk).toUnit
  have hu : u ∈ OrthogonalBracketUnitCompactness.Construction.orthogonalBracketUnitGroup B := hk
  have hAu : OperatorExponentialUnits.Construction.operatorExpUnit A ∈ CommutingExponentialSubgroup.Construction.commutingExponentialSubgroup a hc :=
    ⟨Multiplicative.ofAdd (⟨A, hA⟩ : a), rfl⟩
  have hAP := Split.FilteredFactorInclusions.Construction.commutingExponentialSubgroup_le_splitFiltered B b w H a ha hc hH heig hAu
  have hnP := Split.FilteredFactorInclusions.Construction.unipotentBracketUnitGroup_le_splitFiltered B b w a hc hn
  refine ⟨u, hu, OperatorExponentialUnits.Construction.operatorExpUnit A * n, Subgroup.mul_mem _ hAP hnP, ?_⟩
  change k * (exp A * (n : L →L[ℝ] L)) = T
  rw [← mul_assoc]
  exact he

theorem bracket_identity_component_subset_splitFiltered_product {m : ℕ}
    (B : L →L[ℝ] L →L[ℝ] L) (a : Submodule ℝ (L →L[ℝ] L)) (H : L →L[ℝ] L)
    (ha : a ≤ RegularSymmetricDerivation.Construction.symmetricDerivationSubmodule B) (hc : ∀ X ∈ a, ∀ Y ∈ a, Commute X Y) (hH : H ∈ a)
    (hsum : DerivationSpectralDecomposition.Construction.bracketDerivationSubmodule B = DerivationSpectralDecomposition.Construction.skewBracketDerivations B ⊔ a ⊔ DerivationSpectralDecomposition.Construction.positiveBracketDerivations B H)
    (b : OrthonormalBasis (Fin m) ℝ L) (w : Fin m → ℝ) (heig : ∀ i, H (b i) = w i • b i) :
    connectedComponent (1 : UnipotentBracketGroup.Construction.continuousBracketUnitGroup B) ⊆
      ((OrthogonalBracketUnitCompactness.Construction.orthogonalBracketUnitGroup B).comap (UnipotentBracketGroup.Construction.continuousBracketUnitGroup B).subtype : Set (UnipotentBracketGroup.Construction.continuousBracketUnitGroup B)) *
        ((Split.FilteredBracketGroup.Construction.splitFilteredBracketUnitGroup B b.toBasis w a hc).comap (UnipotentBracketGroup.Construction.continuousBracketUnitGroup B).subtype :
          Set (UnipotentBracketGroup.Construction.continuousBracketUnitGroup B)) := by
  apply Bracket.SubgroupLocalProduct.Construction.bracket_identity_component_subset_product B (OrthogonalBracketUnitCompactness.Construction.orthogonalBracketUnitGroup B)
    (Split.FilteredBracketGroup.Construction.splitFilteredBracketUnitGroup B b.toBasis w a hc) (fun _ hg => hg.1) inf_le_left
    (OrthogonalBracketUnitCompactness.Construction.orthogonalBracketUnitGroup_isCompact B)
    (Split.FilteredBracketGroup.Construction.splitFilteredBracketUnitGroup_isClosed B b.toBasis w a (fun _ hx => (ha hx).1) hc)
  exact bracket_local_splitFiltered_product B a H ha hc hH hsum b w heig

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.LocalSplitFilteredProduct.Construction
