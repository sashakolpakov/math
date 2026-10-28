import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.SplitHeckeChoices
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.CorrespondenceFibers

/-! # Choice Multisets -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.ChoiceMultisets.Construction

noncomputable section

/-!
The raw split support and its subgroup-choice parametrization give the
same target multiset. Repeated target values are retained, and no degree
or volume factor occurs in the reindexing.
-/

variable (s q : ℕ) [Fact q.Prime]

instance splitRawSupport_finite (t : TateComparison.Local.LocalType s) :
    Finite (Hecke.Construction.rawRightCosetSupport (TateComparison.HeckeKernel.integralLevel s q) (TateComparison.HeckeKernel.representative s q t)) :=
  (SplitHeckeTopology.Construction.split_rawRightCosetSupport_finite s q (TateComparison.HeckeKernel.representative s q t)).to_subtype

theorem splitSubgroupChoices_finite (h : ℕ) (a : Fin s → Fin 3 → ℕ)
    (ha : ∀ v i, a v i ≤ h) (hdominant : ∀ v, Antitone (a v)) (h_ElementaryDivisors : ElementaryDivisors.Construction.ElementaryDivisorsInput.{0}) :
    Finite (∀ v : Fin s, BlockHeckeChoices.Construction.BlockSubgroupChoices q h (a v)) :=
  Finite.of_equiv _ (SplitHeckeChoices.Construction.splitRawSubgroupChoicesEquiv s q h a ha hdominant h_ElementaryDivisors)

def rawSplitTargetMultiset {X : Type*} (t : TateComparison.Local.LocalType s)
    (target : Hecke.Construction.rawRightCosetSupport (TateComparison.HeckeKernel.integralLevel s q) (TateComparison.HeckeKernel.representative s q t) → X) : Multiset X :=
  CorrespondenceFibers.Construction.finiteTargetMultiset target

/-- Reindexing raw targets by actual subgroup choices preserves every
target occurrence, including distinct kernels with equal target values. -/
theorem raw_split_multiset_via_subgroups {X : Type*}
    (h : ℕ) (a : Fin s → Fin 3 → ℕ)
    (ha : ∀ v i, a v i ≤ h) (hdominant : ∀ v, Antitone (a v)) (h_ElementaryDivisors : ElementaryDivisors.Construction.ElementaryDivisorsInput.{0})
    (target : Hecke.Construction.rawRightCosetSupport (TateComparison.HeckeKernel.integralLevel s q)
      (TateComparison.HeckeKernel.representative s q (SplitHeckeChoices.Construction.naturalIntegralLocalType s h a hdominant)) → X) :
    letI : Finite (∀ v : Fin s, BlockHeckeChoices.Construction.BlockSubgroupChoices q h (a v)) :=
      splitSubgroupChoices_finite s q h a ha hdominant h_ElementaryDivisors
    rawSplitTargetMultiset s q (SplitHeckeChoices.Construction.naturalIntegralLocalType s h a hdominant) target =
      CorrespondenceFibers.Construction.finiteTargetMultiset (target ∘ (SplitHeckeChoices.Construction.splitRawSubgroupChoicesEquiv s q h a ha hdominant h_ElementaryDivisors).symm) := by
  let : Finite (∀ v : Fin s, BlockHeckeChoices.Construction.BlockSubgroupChoices q h (a v)) :=
    splitSubgroupChoices_finite s q h a ha hdominant h_ElementaryDivisors
  exact CorrespondenceFibers.Construction.finiteTargetMultiset_reindex
    (SplitHeckeChoices.Construction.splitRawSubgroupChoicesEquiv s q h a ha hdominant h_ElementaryDivisors) target

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.ChoiceMultisets.Construction
