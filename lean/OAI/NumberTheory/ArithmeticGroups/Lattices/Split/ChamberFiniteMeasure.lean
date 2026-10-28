import OAI.NumberTheory.ArithmeticGroups.Lattices.AdditiveSplitProductCoordinates
import OAI.NumberTheory.ArithmeticGroups.Lattices.ExponentialLinearCharacter
import OAI.NumberTheory.ArithmeticGroups.Lattices.UnipotentConjugationHaarScaling
import OAI.NumberTheory.ArithmeticGroups.Lattices.UnipotentExponentialInverseMeasure
import OAI.NumberTheory.ArithmeticGroups.Lattices.Split.ProductInvariantDensity

/-! # Chamber Finite Measure -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices

noncomputable section

section

/-! The density exp(positiveTrace A) in split/unipotent coordinates
gives a right-invariant measure on the actual split filtered subgroup. -/

open _root_.MeasureTheory _root_.MeasureTheory.Measure

variable {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℝ L] [FiniteDimensional ℝ L]
  {B : L →L[ℝ] L →L[ℝ] L}

local instance Split.ChamberFiniteMeasure.Construction.splitMeasureEnd_normed : NormedAddCommGroup (L →L[ℝ] L) := inferInstance
local instance Split.ChamberFiniteMeasure.Construction.splitMeasureEnd_space : NormedSpace ℝ (L →L[ℝ] L) := inferInstance
local instance Split.ChamberFiniteMeasure.Construction.splitMeasureEnd_finite : FiniteDimensional ℝ (L →L[ℝ] L) := inferInstance

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

def KillingSplit.Construction.KillingSplitWeightData.splitExponentialMeasure
    (μ : Measure d.subspace) (ν : Measure (DerivationSpectralDecomposition.Construction.positiveBracketDerivations B d.regularElement.val)) :
    Measure (Split.FilteredBracketGroup.Construction.splitFilteredBracketUnitGroup B d.basis.toBasis (fun i => d.weight i d.regularElement)
      d.subspace d.commute) :=
  (((show Measure (Multiplicative d.subspace) from μ).withDensity (ExponentialLinearCharacter.Construction.exponentialLinearCharacter d.positiveTrace)).prod
    (ν.map d.positiveUnipotentExpHomeomorph)).map d.additiveSplitProductHomeomorph

theorem KillingSplit.Construction.KillingSplitWeightData.splitExponentialMeasure_isMulRightInvariant
    (hB : ContinuousBracketConstraints.Construction.IsContinuousLieBracket B) (hK : (ContinuousInnerDerivations.Construction.continuousBracketKillingForm B).Nondegenerate)
    (μ : Measure d.subspace) [IsAddHaarMeasure μ]
    (ν : Measure (DerivationSpectralDecomposition.Construction.positiveBracketDerivations B d.regularElement.val)) [IsAddHaarMeasure ν] :
    IsMulRightInvariant (d.splitExponentialMeasure μ ν) := by
  have hμ : SFinite μ := inferInstance
  let : SFinite (show Measure (Multiplicative d.subspace) from μ) := hμ
  let := MultiplicativeMeasurableSpace.Construction.additiveHaar_isMulRightInvariant_multiplicative μ
  let := d.positiveUnipotentExp_isMulRightInvariant ν
  exact Split.ProductInvariantDensity.Construction.split_product_weighted_measure_right_invariant d.additiveSplitHom d.unipotentSplitHom
    d.additiveSplitProductHomeomorph.toMeasurableEquiv d.additiveSplitProductHomeomorph_mul
    (fun A => d.unipotentConjugation (-A.toAdd))
    (fun A => (d.unipotentConjugation (-A.toAdd)).continuous.measurable)
    d.additiveSplitProduct_conjugation (ExponentialLinearCharacter.Construction.exponentialLinearCharacter d.positiveTrace)
    (ExponentialLinearCharacter.Construction.exponentialLinearCharacter_continuous d.positiveTrace).measurable μ
    (ν.map d.positiveUnipotentExpHomeomorph)
    (fun A => d.unipotentNegativeConjugation_map_expHaar hB hK ν A.toAdd)

end

/-! The positive exponential density has finite mass on the truncated
negative chamber; compact unipotent factors give finite product mass. -/

open _root_.MeasureTheory _root_.MeasureTheory.Measure
open scoped ENNReal

variable {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℝ L] [FiniteDimensional ℝ L]
  {B : L →L[ℝ] L →L[ℝ] L}

local instance Split.ChamberFiniteMeasure.Construction.chamberMeasureEnd_normed : NormedAddCommGroup (L →L[ℝ] L) := inferInstance
local instance Split.ChamberFiniteMeasure.Construction.chamberMeasureEnd_space : NormedSpace ℝ (L →L[ℝ] L) := inferInstance
local instance Split.ChamberFiniteMeasure.Construction.chamberMeasureEnd_finite : FiniteDimensional ℝ (L →L[ℝ] L) := inferInstance

theorem KillingSplit.Construction.KillingSplitWeightData.truncatedNegativeChamber_isClosed
    (d : KillingSplit.Construction.KillingSplitWeightData B) (t : ℝ) : IsClosed (d.truncatedNegativeChamber t) := by
  change IsClosed {A | ∀ i : d.PositiveIndex, d.weight i.val A ≤ t}
  simp only [Set.ofPred_forall]
  exact isClosed_iInter (fun i => isClosed_le (d.weight i.val).continuous_of_finiteDimensional continuous_const)

theorem KillingSplit.Construction.KillingSplitWeightData.positiveDensity_chamber_lt_top
    (d : KillingSplit.Construction.KillingSplitWeightData B) [MeasurableSpace d.subspace] [BorelSpace d.subspace]
    (μ : Measure d.subspace) [IsAddHaarMeasure μ] (t : ℝ) (ht : 0 ≤ t) :
    (μ.withDensity (fun A => ENNReal.ofReal (Real.exp (d.positiveTrace A))))
      (d.truncatedNegativeChamber t) < ∞ := by
  rw [withDensity_apply _ (d.truncatedNegativeChamber_isClosed t).measurableSet]
  exact (lintegral_ofReal_le_lintegral_enorm _).trans_lt (d.integrable_positive_density μ t ht).2

def KillingSplit.Construction.KillingSplitWeightData.splitSiegelSet (d : KillingSplit.Construction.KillingSplitWeightData B) (t : ℝ)
    (S : Set (UnipotentBracketGroup.Construction.unipotentBracketUnitGroup B d.basis (fun i => d.weight i d.regularElement))) :
    Set (Split.FilteredBracketGroup.Construction.splitFilteredBracketUnitGroup B d.basis.toBasis (fun i => d.weight i d.regularElement)
      d.subspace d.commute) :=
  d.additiveSplitProductHomeomorph ''
    ((show Set (Multiplicative d.subspace) from d.truncatedNegativeChamber t) ×ˢ S)

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

theorem KillingSplit.Construction.KillingSplitWeightData.splitSiegelSet_expMeasure_lt_top
    (μ : Measure d.subspace) [IsAddHaarMeasure μ]
    (ν : Measure (DerivationSpectralDecomposition.Construction.positiveBracketDerivations B d.regularElement.val)) [IsAddHaarMeasure ν]
    (t : ℝ) (ht : 0 ≤ t)
    (S : Set (UnipotentBracketGroup.Construction.unipotentBracketUnitGroup B d.basis (fun i => d.weight i d.regularElement)))
    (hS : IsCompact S) : d.splitExponentialMeasure μ ν (d.splitSiegelSet t S) < ∞ := by
  let ρ := ((show Measure (Multiplicative d.subspace) from μ).withDensity
    (ExponentialLinearCharacter.Construction.exponentialLinearCharacter d.positiveTrace)).prod (ν.map d.positiveUnipotentExpHomeomorph)
  let C := (show Set (Multiplicative d.subspace) from d.truncatedNegativeChamber t) ×ˢ S
  have hm : d.splitExponentialMeasure μ ν (d.splitSiegelSet t S) = ρ C := by
    have hmap : (ρ.map d.additiveSplitProductHomeomorph) (d.additiveSplitProductHomeomorph '' C) =
        ρ (d.additiveSplitProductHomeomorph ⁻¹' (d.additiveSplitProductHomeomorph '' C)) :=
      d.additiveSplitProductHomeomorph.toMeasurableEquiv.map_apply _
    simpa only [Set.preimage_image_eq _ d.additiveSplitProductHomeomorph.injective] using! hmap
  rw [hm, Measure.prod_prod]
  apply ENNReal.mul_lt_top
  · exact d.positiveDensity_chamber_lt_top μ t ht
  · let := d.positiveUnipotentExp_isHaarMeasure ν
    exact hS.measure_lt_top

end

end OAI.NumberTheory.ArithmeticGroups.Lattices
