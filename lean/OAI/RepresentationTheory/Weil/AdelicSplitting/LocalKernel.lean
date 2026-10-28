import OAI.RepresentationTheory.Weil.UnitarySplitting.Kernel
import OAI.RepresentationTheory.Weil.AdelicSplitting.FourierRelations
import OAI.RepresentationTheory.Weil.AdelicSplitting.Scalars

/-! # Local Kernel -/

namespace OAI.RepresentationTheory.Weil.AdelicSplitting.LocalKernel.Construction

noncomputable section

/-! Exact scalarity of the local oscillator kernels. The analytic
commutant theorem is reused from the committed UnitarySplitting proof helpers; the
AdelicSplitting completion and normalization hypotheses are discharged here. -/

open scoped _root_.NumberField

theorem localCover_kernel_circle
    {k : Type} [NormedField k] [CompleteSpace k] [LocallyCompactSpace k] [CharZero k]
    [MeasurableSpace k] [BorelSpace k] {N : ℕ}
    (hk : ¬ DiscreteTopology k) (ψ : AddChar k ℂ)
    (hc : Continuous ψ) (hu : ∀ t, ‖ψ t‖ = 1) (hn : ∃ t, ψ t ≠ 1)
    (a : Oscillator.Construction.LocalCover k N ψ) (ha : Oscillator.Construction.localProjection k N ψ a = 1) :
    ∃ z : Circle, Oscillator.Construction.localScalar k N ψ z = a := by
  let T := UnitarySplitting.HeisenbergStability.Construction.heisenbergOperator (d := N) hk ψ hc hu
  have hComm (v : Local.FunctionsMetaplectic.Construction.PhaseSpace k N) (f : Local.FunctionsMetaplectic.Construction.schwartzBruhat k N) :
      a.val.2 (T v f) = T v (a.val.2 f) := by
    have hv : Local.FunctionsMetaplectic.Construction.heisenbergGraph ψ v f (T v f) := rfl
    have hh := (a.property.2 v f (T v f)).mp hv
    change (a.val.2 (T v f)).val = Local.FunctionsMetaplectic.Construction.heisenbergFunction ψ (Local.FunctionsMetaplectic.Construction.symplecticAction a.val.1 v) (a.val.2 f).val at hh
    have hp : a.val.1 = 1 := ha
    rw [hp, Local.FunctionsMetaplectic.Construction.symplecticAction_one] at hh
    exact Subtype.ext hh
  obtain ⟨z, hz⟩ := UnitarySplitting.Kernel.Construction.unitary_heisenberg_commutant_scalar
    hk ψ hc hu hn a.val.2.toLinearMap a.property.1 hComm
  refine ⟨z, ?_⟩
  apply Subtype.ext
  apply Prod.ext
  · exact ha.symm
  · apply LinearEquiv.ext
    intro f
    exact (hz f).symm

theorem completion_nondiscrete (F : Type) [Field F] [NumberField F] (v : ArchimedeanAdeles.Construction.Places F) :
    ¬ DiscreteTopology (ArchimedeanAdeles.Construction.Completion F v) := by
  intro h
  let : DiscreteTopology (ArchimedeanAdeles.Construction.Completion F v) := h
  cases v with
  | inl v =>
      rcases v.isReal_or_isComplex with hv | hv
      · let : DiscreteTopology ℝ :=
          (NumberField.InfinitePlace.Completion.isometryEquivRealOfIsReal hv).toHomeomorph.discreteTopology
        have : Subsingleton ℝ := subsingleton_of_preconnected_totallyDisconnected
        exact zero_ne_one (Subsingleton.elim (0 : ℝ) 1)
      · let : DiscreteTopology ℂ :=
          (NumberField.InfinitePlace.Completion.isometryEquivComplexOfIsComplex hv).toHomeomorph.discreteTopology
        have : Subsingleton ℂ := subsingleton_of_preconnected_totallyDisconnected
        exact zero_ne_one (Subsingleton.elim (0 : ℂ) 1)
  | inr v =>
      let : CharZero (v.adicCompletion F) := ArchimedeanAdeles.Construction.completionCharZero F (.inr v)
      have he : (v.adicCompletionIntegers F : Set (v.adicCompletion F)) =
          Metric.closedBall (0 : v.adicCompletion F) 1 := by
        ext x
        simp only [Metric.mem_closedBall, dist_zero_right,
          Valued.toNormedField.norm_le_one_iff]
        rfl
      have hc : IsCompact (v.adicCompletionIntegers F : Set (v.adicCompletion F)) := by
        rw [he]
        exact isCompact_closedBall _ _
      have hf := hc.finite_of_discrete
      have hinf : Set.Infinite (Set.range (fun z : ℤ => (z : v.adicCompletion F))) :=
        Set.infinite_range_of_injective Int.cast_injective
      apply hinf
      apply hf.subset
      rintro _ ⟨z, rfl⟩
      exact intCast_mem (v.adicCompletionIntegers F).toSubring z

theorem normalized_localCover_kernel_circle
    (F : Type) [Field F] [NumberField F] (d : F) (hd : d ≠ 0)
    (n m : ℕ) (hN : 0 < n * m)
    (H : (Matrix (Fin n) (Fin n) (UnitaryBase.Construction.Quadratic F d))ˣ)
    (K : (Matrix (Fin m) (Fin m) (UnitaryBase.Construction.Quadratic F d))ˣ)
    (C : Characters.Construction.GlobalCharacters F d n m) (P : Assembly.Construction.GlobalFrames F d n m H K)
    (D : Assembly.Construction.NormalizedLocalSplittings F d n m H K hd C P)
    (v : ArchimedeanAdeles.Construction.Places F) (a : Vacuum.Construction.CoverAt F (n * m) C.ψ v)
    (ha : Vacuum.Construction.projectionAt F (n * m) C.ψ v a = 1) :
    ∃ z : Circle, Vacuum.Construction.scalarAt F (n * m) C.ψ v z = a :=
  localCover_kernel_circle (completion_nondiscrete F v) (Characters.Construction.localAdditiveCharacter F C.ψ v)
    (Characters.Construction.localAdditiveCharacter_continuous F C.ψ C.ψ_continuous v)
    (Characters.Construction.localAdditiveCharacter_unitary F C.ψ C.ψ_unitary v)
    (NontrivialLocalCharacter.Construction.normalizedLocalSplittings_character_nontrivial F d hd n m hN H K C P D v) a ha

end

end OAI.RepresentationTheory.Weil.AdelicSplitting.LocalKernel.Construction
