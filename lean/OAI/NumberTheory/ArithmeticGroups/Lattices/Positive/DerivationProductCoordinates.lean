import OAI.NumberTheory.ArithmeticGroups.Lattices.Positive.DerivationInvariantComplement
import OAI.NumberTheory.ArithmeticGroups.Lattices.Weight.RaisingProductCoordinates

/-! # Derivation Product Coordinates -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.Positive.DerivationProductCoordinates.Construction

noncomputable section

/-! Global complementary product coordinates for the actual positive
bracket derivations, with the complement derived from split symmetry. -/

open NormedSpace

variable {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℝ L] [FiniteDimensional ℝ L]

local instance positiveProductEnd_normed : NormedAddCommGroup (L →L[ℝ] L) := inferInstance
local instance positiveProductEnd_space : NormedSpace ℝ (L →L[ℝ] L) := inferInstance
local instance positiveProductEnd_finite : FiniteDimensional ℝ (L →L[ℝ] L) := inferInstance

theorem positive_derivations_exists_complementary_product_coordinates
    {m : ℕ} (B : L →L[ℝ] L →L[ℝ] L) (b : OrthonormalBasis (Fin m) ℝ L)
    (H : L →L[ℝ] L) (hH : H ∈ RegularSymmetricDerivation.Construction.symmetricDerivationSubmodule B)
    (w : Fin m → ℝ) (heig : ∀ i, H (b i) = w i • b i) :
    ∃ U : Submodule ℝ (DerivationNilpotence.Construction.weightRaisingOperators b w),
      IsCompl U (DerivationInvariantComplement.Construction.positiveDerivationsInWeightRaising B b H w) ∧
      (∀ t X, X ∈ U → Weight.RaisingSplitFlow.Construction.weightRaisingSplitFlow b H hH.1 w heig t X ∈ U) ∧
      ∃ e : U × DerivationInvariantComplement.Construction.positiveDerivationsInWeightRaising B b H w ≃ₜ DerivationNilpotence.Construction.weightRaisingOperators b w,
        ∀ p, (e p).val = exp p.1.val.val * exp p.2.val.val - 1 := by
  obtain ⟨U, hUV, hU⟩ := DerivationInvariantComplement.Construction.positive_derivations_exists_split_invariant_complement B b H hH w heig
  obtain ⟨e, he⟩ := Weight.RaisingProductCoordinates.Construction.weightRaising_exists_exponential_product_homeomorph b H hH.1 w heig
    U (DerivationInvariantComplement.Construction.positiveDerivationsInWeightRaising B b H w) hUV hU
    (DerivationInvariantComplement.Construction.positiveDerivationsInWeightRaising_split_invariant B b H hH w heig)
  exact ⟨U, hUV, hU, e, he⟩

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.Positive.DerivationProductCoordinates.Construction
