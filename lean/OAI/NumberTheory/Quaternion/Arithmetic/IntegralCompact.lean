import OAI.NumberTheory.Quaternion.Arithmetic.LocalAdeles
import OAI.NumberTheory.ArithmeticGroups.Lattices.Realizations
import OAI.RepresentationTheory.Weil.AdelicSplitting.LocalCompact

/-! # Integral Compact -/

namespace OAI.NumberTheory.Quaternion.Arithmetic.IntegralCompact

noncomputable section

section

/-! Hausdorffness and second countability for the actual completed point
groups. A countable dense field supplies separability of each completion. -/

open scoped Classical _root_.NumberField
open _root_.TopologicalSpace

variable {F : Type} [Field F] [NumberField F]

instance completionT2Space (v : LocalAdeles.Place F) : T2Space (LocalAdeles.Completion v) := by
  cases v with
  | inl v => exact inferInstanceAs (T2Space v.Completion)
  | inr v => exact inferInstanceAs (T2Space (v.adicCompletion F))

instance completionSecondCountable (v : LocalAdeles.Place F) : SecondCountableTopology (LocalAdeles.Completion v) := by
  let : Countable F := Finsupp.Countable.of_moduleFinite (R := ℚ) (M := F)
  cases v with
  | inl v =>
    let : Countable (WithAbs v.val) := (WithAbs.equiv v.val).injective.countable
    let : SeparableSpace v.Completion :=
      (NumberField.InfinitePlace.Completion.denseRange_coe v).separableSpace'
    exact inferInstanceAs (SecondCountableTopology v.Completion)
  | inr v =>
    let : SeparableSpace (v.adicCompletion F) :=
      (v.denseRange_algebraMap F).separableSpace'
    exact inferInstanceAs (SecondCountableTopology (v.adicCompletion F))

instance completionLocallyCompact (v : LocalAdeles.Place F) : LocallyCompactSpace (LocalAdeles.Completion v) := by
  cases v with
  | inl v => exact inferInstanceAs (LocallyCompactSpace v.Completion)
  | inr v => exact inferInstanceAs (LocallyCompactSpace (v.adicCompletion F))

variable {n : ℕ} (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n)

instance localPointsSecondCountable (v : LocalAdeles.Place F) : SecondCountableTopology (LocalAdeles.LocalPoints G v) :=
  inferInstanceAs (SecondCountableTopology (G.Points (LocalAdeles.localEmbedding v)))

instance localPointsT2Space (v : LocalAdeles.Place F) : T2Space (LocalAdeles.LocalPoints G v) :=
  inferInstanceAs (T2Space (G.Points (LocalAdeles.localEmbedding v)))

instance localPointsLocallyCompact (v : LocalAdeles.Place F) : LocallyCompactSpace (LocalAdeles.LocalPoints G v) :=
  inferInstanceAs (LocallyCompactSpace (G.Points (LocalAdeles.localEmbedding v)))

theorem localPoints_closedEmbedding (v : LocalAdeles.Place F) :
    Topology.IsClosedEmbedding
      (fun g : LocalAdeles.LocalPoints G v => (g.val : Matrix (Fin n) (Fin n) (LocalAdeles.Completion v))) :=
  G.points_isClosedEmbedding (LocalAdeles.localEmbedding v)

end

/-! Compactness of the finite-place integral groups in the fixed matrix
realization, and the resulting finite-index property of open subgroups. -/

open scoped Classical _root_.NumberField
open IsDedekindDomain Set _root_.Topology

variable {F : Type} [Field F] [NumberField F] {n : ℕ}

theorem finiteLocalIntegerRing_isCompact (v : HeightOneSpectrum (𝓞 F)) :
    IsCompact (LocalAdeles.localIntegerRing (Sum.inr v) : Set (LocalAdeles.Completion (Sum.inr v))) := by
  have hc : CompactSpace (v.adicCompletionIntegers F) :=
    Valued.integer.properSpace_iff_compactSpace_integer.mp inferInstance
  exact isCompact_iff_compactSpace.mpr hc

theorem integralLocalSubgroup_isCompact (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n)
    (v : HeightOneSpectrum (𝓞 F)) :
    IsCompact (LocalAdeles.integralLocalSubgroup G (Sum.inr v) : Set (LocalAdeles.LocalPoints G (Sum.inr v))) := by
  have hmatrix : IsCompact {a : Matrix (Fin n) (Fin n) (LocalAdeles.Completion (Sum.inr v)) |
      ∀ i j, a i j ∈ LocalAdeles.localIntegerRing (Sum.inr v)} := by
    exact (finiteLocalIntegerRing_isCompact v).matrix
  have hpre := (localPoints_closedEmbedding G (Sum.inr v)).isCompact_preimage hmatrix
  apply hpre.of_isClosed_subset
  · exact (LocalAdeles.integralLocalSubgroup G (Sum.inr v)).isClosed_of_isOpen
      (LocalAdeles.integralLocalSubgroup_isOpen G (Sum.inr v))
  · intro g hg
    exact hg.1

theorem finiteIndex_of_open_in_compact_group {K : Type*} [Group K]
    [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K]
    (H : Subgroup K) (hH : IsOpen (H : Set K)) : H.FiniteIndex := by
  let : DiscreteTopology (K ⧸ H) := QuotientGroup.discreteTopology hH
  let : Finite (K ⧸ H) := finite_of_compact_of_discrete
  exact Subgroup.finiteIndex_of_finite_quotient

end

end OAI.NumberTheory.Quaternion.Arithmetic.IntegralCompact
