import OAI.NumberTheory.ArithmeticGroups.Lattices.Split.ExponentialHaar
import OAI.NumberTheory.ArithmeticGroups.Lattices.Split.ChamberFiniteMeasure
import OAI.NumberTheory.ArithmeticGroups.Lattices.HaarFiniteMeasureTransfer

/-! # Siegel Finite Volume -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices

noncomputable section

/-! Intrinsic split Siegel sets have finite right Haar volume. -/

open _root_.MeasureTheory _root_.MeasureTheory.Measure

variable {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℝ L] [FiniteDimensional ℝ L]
  {B : L →L[ℝ] L →L[ℝ] L}

local instance Split.SiegelFiniteVolume.Construction.siegelVolumeEnd_normed : NormedAddCommGroup (L →L[ℝ] L) := inferInstance
local instance Split.SiegelFiniteVolume.Construction.siegelVolumeEnd_space : NormedSpace ℝ (L →L[ℝ] L) := inferInstance
local instance Split.SiegelFiniteVolume.Construction.siegelVolumeEnd_finite : FiniteDimensional ℝ (L →L[ℝ] L) := inferInstance

theorem KillingSplit.Construction.KillingSplitWeightData.splitSiegelSet_isClosed (d : KillingSplit.Construction.KillingSplitWeightData B) (t : ℝ)
    (S : Set (UnipotentBracketGroup.Construction.unipotentBracketUnitGroup B d.basis (fun i => d.weight i d.regularElement)))
    (hS : IsCompact S) : IsClosed (d.splitSiegelSet t S) :=
  d.additiveSplitProductHomeomorph.isClosedMap _ ((d.truncatedNegativeChamber_isClosed t).prod hS.isClosed)

variable (d : KillingSplit.Construction.KillingSplitWeightData B)
  [MeasurableSpace d.subspace] [BorelSpace d.subspace]
  [MeasurableSpace (DerivationSpectralDecomposition.Construction.positiveBracketDerivations B d.regularElement.val)]
  [BorelSpace (DerivationSpectralDecomposition.Construction.positiveBracketDerivations B d.regularElement.val)]
  [MeasurableSpace (UnipotentBracketGroup.Construction.unipotentBracketUnitGroup B d.basis (fun i => d.weight i d.regularElement))]
  [BorelSpace (UnipotentBracketGroup.Construction.unipotentBracketUnitGroup B d.basis (fun i => d.weight i d.regularElement))]
  [MeasurableSpace (Split.FilteredBracketGroup.Construction.splitFilteredBracketUnitGroup B d.basis.toBasis (fun i => d.weight i d.regularElement)
    d.subspace d.commute)]
  [BorelSpace (Split.FilteredBracketGroup.Construction.splitFilteredBracketUnitGroup B d.basis.toBasis (fun i => d.weight i d.regularElement)
    d.subspace d.commute)]

theorem KillingSplit.Construction.KillingSplitWeightData.splitSiegelSet_inverseHaar_lt_top
    (hB : ContinuousBracketConstraints.Construction.IsContinuousLieBracket B) (hK : (ContinuousInnerDerivations.Construction.continuousBracketKillingForm B).Nondegenerate)
    (ρ : Measure (Split.FilteredBracketGroup.Construction.splitFilteredBracketUnitGroup B d.basis.toBasis (fun i => d.weight i d.regularElement)
      d.subspace d.commute)) [IsHaarMeasure ρ]
    (t : ℝ) (ht : 0 ≤ t)
    (S : Set (UnipotentBracketGroup.Construction.unipotentBracketUnitGroup B d.basis (fun i => d.weight i d.regularElement)))
    (hS : IsCompact S) : ρ.inv (d.splitSiegelSet t S) < ⊤ := by
  let : LocallyCompactSpace
      (Split.FilteredBracketGroup.Construction.splitFilteredBracketUnitGroup B d.basis.toBasis (fun i => d.weight i d.regularElement)
        d.subspace d.commute) := d.splitExponentialHomeomorph.symm.isClosedEmbedding.locallyCompactSpace
  let : SecondCountableTopology
      (Split.FilteredBracketGroup.Construction.splitFilteredBracketUnitGroup B d.basis.toBasis (fun i => d.weight i d.regularElement)
        d.subspace d.commute) := d.splitExponentialHomeomorph.symm.secondCountableTopology
  let μ := addHaar (G := d.subspace)
  let ν := addHaar (G := DerivationSpectralDecomposition.Construction.positiveBracketDerivations B d.regularElement.val)
  let := d.splitExponentialMeasure_inv_isHaarMeasure hB hK μ ν
  exact HaarFiniteMeasureTransfer.Construction.inverseHaar_finite_of_rightHaar_finite ρ (d.splitExponentialMeasure μ ν) _
    (d.splitSiegelSet_expMeasure_lt_top μ ν t ht S hS)

end

end OAI.NumberTheory.ArithmeticGroups.Lattices
