import OAI.NumberTheory.ArithmeticGroups.Lattices.RegularWeightsCentralizer
import OAI.NumberTheory.ArithmeticGroups.Lattices.LinearIwasawaDecomposition

/-! # Killing Split -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.KillingSplit.Construction

noncomputable section

/-! Compatible split weights, opposite roots, and a regular element
for a real Lie algebra with nondegenerate Killing form. -/

open scoped Classical
open _root_.ContinuousLinearMap

variable {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℝ L] [FiniteDimensional ℝ L]

structure KillingSplitWeightData (B : L →L[ℝ] L →L[ℝ] L) where
  subspace : Submodule ℝ (L →L[ℝ] L)
  basis : OrthonormalBasis (Fin (Module.finrank ℝ L)) ℝ L
  weight : Fin (Module.finrank ℝ L) → Module.Dual ℝ subspace
  regularElement : subspace
  le_symmetric : subspace ≤ RegularSymmetricDerivation.Construction.symmetricDerivationSubmodule B
  commute : ∀ A ∈ subspace, ∀ C ∈ subspace, Commute A C
  eigenvector : ∀ i (A : subspace), A.val (basis i) = weight i A • basis i
  regular : ∀ i, weight i regularElement = 0 ↔ weight i = 0
  opposite : ∀ i, ∃ j, weight j = -weight i
  centralizer : ∀ X ∈ RegularSymmetricDerivation.Construction.symmetricDerivationSubmodule B,
    Commute regularElement.val X ↔ X ∈ subspace

theorem exists_killing_split_weight_data
    (B : L →L[ℝ] L →L[ℝ] L) (hB : ContinuousBracketConstraints.Construction.IsContinuousLieBracket B)
    (hK : (ContinuousInnerDerivations.Construction.continuousBracketKillingForm B).Nondegenerate) : Nonempty (KillingSplitWeightData B) := by
  obtain ⟨a, ha, hc, hmax⟩ := MaximalCommutingSubspace.Construction.exists_maximal_commuting_subspace (RegularSymmetricDerivation.Construction.symmetricDerivationSubmodule B)
  obtain ⟨b, w, heig⟩ := CommutingSymmetricWeights.Construction.exists_commuting_symmetric_weights a (fun A hA => (ha hA).1) hc
  obtain ⟨H, hH⟩ := RegularLinearForms.Construction.exists_regular_linear_forms w
  have hopp := InvariantFormWeightPairing.Construction.invariant_form_weights_opposite a b w heig (ContinuousInnerDerivations.Construction.continuousBracketKillingForm B) hK
    (fun A x y => FaithfulDerivationCommutator.Construction.continuousBracketKillingForm_derivation B A.val (ha A.property).2 x y)
  exact ⟨⟨a, b, w, H, ha, hc, heig, hH, hopp,
    RegularWeightsCentralizer.Construction.killing_regular_weights_centralizer B hB hK a ha hc hmax b w heig H hH⟩⟩

theorem KillingSplitWeightData.positive_separating
    {B : L →L[ℝ] L →L[ℝ] L} (d : KillingSplitWeightData B) :
    ∀ A : d.subspace,
      (∀ i : {i : Fin (Module.finrank ℝ L) // 0 < d.weight i d.regularElement},
        d.weight i.val A = 0) → A = 0 :=
  RegularLinearForms.Construction.positive_linear_forms_separate d.weight
    (InvariantFormWeightPairing.Construction.eigenbasis_weights_separate d.subspace d.basis d.weight d.eigenvector)
    d.opposite d.regularElement d.regular

theorem KillingSplitWeightData.linear_iwasawa
    {B : L →L[ℝ] L →L[ℝ] L} (d : KillingSplitWeightData B)
    (hadj : ∀ X, Lie.AutomorphismTransversal.Construction.continuousBilinearDerivationDefect B X = 0 →
      Lie.AutomorphismTransversal.Construction.continuousBilinearDerivationDefect B (adjoint X) = 0) :
    DerivationSpectralDecomposition.Construction.bracketDerivationSubmodule B = DerivationSpectralDecomposition.Construction.skewBracketDerivations B ⊔ d.subspace ⊔
      DerivationSpectralDecomposition.Construction.positiveBracketDerivations B d.regularElement.val := by
  let : CompleteSpace L := FiniteDimensional.complete ℝ L
  rw [DerivationSpectralDecomposition.Construction.bracket_derivation_spectral_decomposition B hadj d.regularElement.val
    (d.le_symmetric d.regularElement.property),
    LinearIwasawaDecomposition.Construction.regular_symmetric_centralizer_submodule B d.subspace d.le_symmetric
      d.regularElement.val d.centralizer]

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.KillingSplit.Construction
