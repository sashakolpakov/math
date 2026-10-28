import OAI.NumberTheory.ArithmeticGroups.Lattices.KillingSplit
import OAI.NumberTheory.ArithmeticGroups.Lattices.PolyhedralExponentialIntegrability

/-! # Chamber Integrability -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.Split.ChamberIntegrability.Construction

noncomputable section

/-! The positive-weight exponential density is integrable on every
upper-truncated negative chamber in the split derivation subspace. -/

open scoped Classical
open _root_.MeasureTheory

variable {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℝ L] [FiniteDimensional ℝ L]
  {B : L →L[ℝ] L →L[ℝ] L}

def _root_.OAI.NumberTheory.ArithmeticGroups.Lattices.KillingSplit.Construction.KillingSplitWeightData.PositiveIndex (d : KillingSplit.Construction.KillingSplitWeightData B) :=
  {i : Fin (Module.finrank ℝ L) // 0 < d.weight i d.regularElement}

instance (d : KillingSplit.Construction.KillingSplitWeightData B) : Fintype d.PositiveIndex :=
  inferInstanceAs (Fintype {i : Fin (Module.finrank ℝ L) // 0 < d.weight i d.regularElement})

def _root_.OAI.NumberTheory.ArithmeticGroups.Lattices.KillingSplit.Construction.KillingSplitWeightData.positiveTrace (d : KillingSplit.Construction.KillingSplitWeightData B) : Module.Dual ℝ d.subspace :=
  ∑ i : d.PositiveIndex, d.weight i.val

def _root_.OAI.NumberTheory.ArithmeticGroups.Lattices.KillingSplit.Construction.KillingSplitWeightData.truncatedNegativeChamber (d : KillingSplit.Construction.KillingSplitWeightData B) (t : ℝ) :
    Set d.subspace := {A | ∀ i : d.PositiveIndex, d.weight i.val A ≤ t}

theorem _root_.OAI.NumberTheory.ArithmeticGroups.Lattices.KillingSplit.Construction.KillingSplitWeightData.integrable_positive_density
    (d : KillingSplit.Construction.KillingSplitWeightData B) [MeasurableSpace d.subspace] [BorelSpace d.subspace]
    (μ : Measure d.subspace) [μ.IsAddHaarMeasure] (t : ℝ) (ht : 0 ≤ t) :
    IntegrableOn (fun A => Real.exp (d.positiveTrace A)) (d.truncatedNegativeChamber t) μ := by
  have hsep : ∀ A : d.subspace,
      (∀ i : d.PositiveIndex, (-d.weight i.val) A = 0) → A = 0 := by
    intro A hA
    apply d.positive_separating A
    intro i
    simpa only [LinearMap.neg_apply, neg_eq_zero] using hA i
  simpa only [KillingSplit.Construction.KillingSplitWeightData.positiveTrace, LinearMap.sum_apply, LinearMap.neg_apply,
    Finset.sum_neg_distrib, neg_neg, neg_le_neg_iff,
    KillingSplit.Construction.KillingSplitWeightData.truncatedNegativeChamber] using
    PolyhedralExponentialIntegrability.Construction.integrableOn_exp_neg_sum_separating_forms μ (fun i : d.PositiveIndex => -d.weight i.val) hsep t ht

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.Split.ChamberIntegrability.Construction
