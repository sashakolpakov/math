import OAI.NumberTheory.ArithmeticGroups.Lattices.LocalSplitFilteredProduct
import OAI.NumberTheory.ArithmeticGroups.Lattices.Bracket.ExponentialComponent

/-! # Global Split Filtered Product -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.GlobalSplitFilteredProduct.Construction

noncomputable section

/-! Cartan decomposition extends the compact/filtered product from the
identity component to every bracket automorphism. -/

open scoped Classical _root_.Matrix.Norms.Operator
open _root_.ContinuousLinearMap

theorem bracket_global_splitFiltered_product
    {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℝ L] [FiniteDimensional ℝ L]
    {m : ℕ} (B : L →L[ℝ] L →L[ℝ] L)
    (hadj : ∀ g : L ≃L[ℝ] L, ContinuousBracketChange.Construction.continuousBracketChange g B = B →
      ∀ x y, adjoint g.toContinuousLinearMap (B x y) =
        B (adjoint g.toContinuousLinearMap x) (adjoint g.toContinuousLinearMap y))
    (a : Submodule ℝ (L →L[ℝ] L)) (H : L →L[ℝ] L)
    (ha : a ≤ RegularSymmetricDerivation.Construction.symmetricDerivationSubmodule B) (hc : ∀ X ∈ a, ∀ Y ∈ a, Commute X Y) (hH : H ∈ a)
    (hsum : DerivationSpectralDecomposition.Construction.bracketDerivationSubmodule B = DerivationSpectralDecomposition.Construction.skewBracketDerivations B ⊔ a ⊔ DerivationSpectralDecomposition.Construction.positiveBracketDerivations B H)
    (b : OrthonormalBasis (Fin m) ℝ L) (w : Fin m → ℝ) (heig : ∀ i, H (b i) = w i • b i)
    (g : (L →L[ℝ] L)ˣ) (hg : g ∈ UnipotentBracketGroup.Construction.continuousBracketUnitGroup B) :
    ∃ k ∈ OrthogonalBracketUnitCompactness.Construction.orthogonalBracketUnitGroup B, ∃ p ∈ Split.FilteredBracketGroup.Construction.splitFilteredBracketUnitGroup B b.toBasis w a hc, k * p = g := by
  obtain ⟨k₀, hk₀, h, hh, hprod⟩ := Bracket.ExponentialComponent.Construction.bracket_automorphism_compact_component B hadj g hg
  obtain ⟨k₁, hk₁, p, hp, he⟩ :=
    LocalSplitFilteredProduct.Construction.bracket_identity_component_subset_splitFiltered_product B a H ha hc hH hsum b w heig hh
  refine ⟨k₀ * k₁.val, Subgroup.mul_mem _ hk₀ hk₁, p.val, hp, ?_⟩
  have he' : k₁.val * p.val = h.val := congrArg Subtype.val he
  rw [mul_assoc, he', ← hprod]

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.GlobalSplitFilteredProduct.Construction
