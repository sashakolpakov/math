import OAI.NumberTheory.ArithmeticGroups.Lattices.TripleExponentialLocalProduct
import OAI.NumberTheory.ArithmeticGroups.Lattices.Weight.RaisingExponential

/-! # Local Iwasawa Product -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.LocalIwasawaProduct.Construction

noncomputable section

/-! The linear Iwasawa decomposition gives a neighborhood of the
identity in compact/split/unipotent product form. -/

open scoped _root_.Topology
open _root_.ContinuousLinearMap NormedSpace Filter

theorem bracket_local_iwasawa_product
    {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℝ L] [FiniteDimensional ℝ L]
    {m : ℕ} (B : L →L[ℝ] L →L[ℝ] L) (a : Submodule ℝ (L →L[ℝ] L))
    (H : L →L[ℝ] L) (ha : a ≤ RegularSymmetricDerivation.Construction.symmetricDerivationSubmodule B) (hH : H ∈ a)
    (hsum : DerivationSpectralDecomposition.Construction.bracketDerivationSubmodule B = DerivationSpectralDecomposition.Construction.skewBracketDerivations B ⊔ a ⊔ DerivationSpectralDecomposition.Construction.positiveBracketDerivations B H)
    (b : OrthonormalBasis (Fin m) ℝ L) (w : Fin m → ℝ)
    (heig : ∀ i, H (b i) = w i • b i) :
    ∀ᶠ T in 𝓝 (1 : L →L[ℝ] L),
      (∀ x y, T (B x y) = B (T x) (T y)) →
      ∃ k ∈ OrthogonalBracketCompactness.Construction.orthogonalBracketOperators B, ∃ A ∈ a,
        ∃ n ∈ UnipotentBracketGroup.Construction.unipotentBracketUnitGroup B b w, k * exp A * (n : L →L[ℝ] L) = T := by
  let : CompleteSpace L := FiniteDimensional.complete ℝ L
  have h := TripleExponentialLocalProduct.Construction.bilinear_stabilizer_local_triple_exponential B (DerivationSpectralDecomposition.Construction.skewBracketDerivations B) a
    (DerivationSpectralDecomposition.Construction.positiveBracketDerivations B H) inf_le_left (fun _ hx => (ha hx).2)
    (InvolutionSpectralDecomposition.Construction.positiveSpectralSubmodule_le _ _) hsum.symm
  filter_upwards [h] with T hT
  intro hTB
  obtain ⟨u, hu, A, hA, v, hv, he⟩ := hT hTB
  have hskew : adjoint u = -u := by
    have hz : adjoint u + u = 0 := hu.2
    exact eq_neg_of_add_eq_zero_left hz
  have hk : exp u ∈ OrthogonalBracketCompactness.Construction.orthogonalBracketOperators B := by
    simpa only [one_smul] using OrthogonalBracketAlgebra.Construction.exp_skew_derivation_mem_orthogonal B u hu.1 hskew 1
  exact ⟨exp u, hk, A, hA, (Bracket.ExponentialEquiv.Construction.continuousLinearMapExpEquiv v).toUnit,
    Weight.RaisingExponential.Construction.positive_derivation_exp_mem_unipotent B b H (ha hH).1 w heig v hv, he⟩

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.LocalIwasawaProduct.Construction
