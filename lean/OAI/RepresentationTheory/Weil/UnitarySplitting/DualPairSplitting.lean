import OAI.RepresentationTheory.Weil.UnitarySplitting.TracePairing
import OAI.RepresentationTheory.Weil.UnitarySplitting.Characters
import OAI.RepresentationTheory.Weil.UnitarySplitting.Oscillator
import OAI.RepresentationTheory.Weil.UnitarySplitting.SymplecticCoordinates
import OAI.RepresentationTheory.Weil.UnitarySplitting.GroupTopology
import OAI.RepresentationTheory.Weil.UnitarySplitting.LocalTest
import OAI.RepresentationTheory.Weil.UnitarySplitting.Heisenberg
import OAI.RepresentationTheory.Weil.UnitarySplitting.UltraMultiplier
import OAI.RepresentationTheory.Weil.UnitarySplitting.DensityMeasure
import OAI.RepresentationTheory.Weil.UnitarySplitting.Kernel
import OAI.RepresentationTheory.Weil.UnitarySplitting.FourierPairing
import OAI.RepresentationTheory.Weil.UnitarySplitting.FrameTransport
import OAI.RepresentationTheory.Weil.UnitarySplitting.UltraSurjectivity
import OAI.RepresentationTheory.Weil.UnitarySplitting.Surjectivity
import OAI.RepresentationTheory.Weil.UnitarySplitting.Generic
import OAI.RepresentationTheory.Weil.UnitarySplitting.HermitianNormForms
import OAI.RepresentationTheory.Weil.UnitarySplitting.NormHaar
import OAI.RepresentationTheory.Weil.UnitarySplitting.NormKernelOpen
import OAI.RepresentationTheory.Weil.UnitarySplitting.NormQuadraticIntegrals
import OAI.RepresentationTheory.Weil.UnitarySplitting.DiagonalNormGaussian
import OAI.RepresentationTheory.Weil.UnitarySplitting.ArchimedeanNormGaussian
import OAI.RepresentationTheory.Weil.UnitarySplitting.WeakGaussianNonzero
import OAI.RepresentationTheory.Weil.UnitarySplitting.WeylSynthesisAdd
import OAI.RepresentationTheory.Weil.UnitarySplitting.WeylSynthesis
import OAI.RepresentationTheory.Weil.UnitarySplitting.WeylResolutionOperator
import OAI.RepresentationTheory.Weil.UnitarySplitting.WeakCayleyTestCoefficients
import OAI.RepresentationTheory.Weil.UnitarySplitting.UltraCayleyLift
import OAI.RepresentationTheory.Weil.UnitarySplitting.CayleyCompositionPhase
import OAI.RepresentationTheory.Weil.UnitarySplitting.UltraCayleyComposition
import OAI.RepresentationTheory.Weil.UnitarySplitting.HermitianGaussianDistribution
import OAI.RepresentationTheory.Weil.UnitarySplitting.CanonicalCayleyLift
import OAI.RepresentationTheory.Weil.UnitarySplitting.GaussianFormula
import OAI.RepresentationTheory.Weil.UnitarySplitting.CayleyGaussianCutoffs
import OAI.RepresentationTheory.Weil.UnitarySplitting.GenericCharacterCorrection
import OAI.RepresentationTheory.Weil.UnitarySplitting.GenericDeterminantCharacter
import OAI.RepresentationTheory.Weil.UnitarySplitting.CayleyLiftContinuity
import OAI.RepresentationTheory.Weil.UnitarySplitting.CayleyCentralizers
import OAI.RepresentationTheory.Weil.UnitarySplitting.Weighted
import OAI.RepresentationTheory.Weil.UnitarySplitting.UltraFactorSplittings
import OAI.RepresentationTheory.Weil.UnitarySplitting.RealWeylCoefficients
import OAI.RepresentationTheory.Weil.UnitarySplitting.PartialSchwartzFourier
import OAI.RepresentationTheory.Weil.UnitarySplitting.RealBilinearFourier
import OAI.RepresentationTheory.Weil.UnitarySplitting.RealCayleyOperator
import OAI.RepresentationTheory.Weil.UnitarySplitting.RealCayleyLift
import OAI.RepresentationTheory.Weil.UnitarySplitting.Archimedean
import Lean.Util.CollectAxioms

/-! # Dual Pair Splitting -/

namespace OAI.RepresentationTheory.Weil.UnitarySplitting.DualPairSplitting.Construction

noncomputable section

/-! The unconditional UnitarySplitting local unitary dual-pair splitting, including every
realization clause of the repaired target. This entry does not import the
statement. Both archimedean and nonarchimedean constructions use actual
Schwartz–Bruhat intertwiners and the prescribed splitting characters.
All imported construction declarations, including generated declarations
and the reused LocalWeil modules, are audited against the classical foundations. -/

theorem coordinate_and_topological_realization
    {F E : Type} [NormedField F] [NormedField E] [Algebra F E]
    [CompleteSpace F] [LocallyCompactSpace F] [CharZero F]
    [FiniteDimensional F E] [MeasurableSpace F] [BorelSpace F]
    (hF : ¬ DiscreteTopology F) (hEmbedding : Continuous (algebraMap F E))
    (hQuadratic : Module.finrank F E = 2) (σ : E ≃ₐ[F] E)
    (m n : ℕ) (H : Matrix (Fin m) (Fin m) E) (K : Matrix (Fin n) (Fin n) E)
    (hHermitian : ∀ i j, H j i = σ (H i j))
    (hSkewHermitian : ∀ i j, K j i = -σ (K i j))
    (hHNondegenerate : H.det ≠ 0) (hKNondegenerate : K.det ≠ 0)
    (ψ : AddChar F ℂ) :
    Nonempty (Oscillator.Construction.SymplecticFrame σ H K) ∧
      ∀ c : Oscillator.Construction.SymplecticFrame σ H K,
        IsTopologicalGroup (Oscillator.Construction.CircleExtension σ H K c ψ) ∧
          Continuous (Oscillator.Construction.circleScalar σ H K c ψ) ∧
          Function.Injective (Oscillator.Construction.circleScalar σ H K c ψ) := by
  refine ⟨SymplecticCoordinates.Construction.symplecticFrame_nonempty hQuadratic σ m n H K hHermitian hSkewHermitian
    hHNondegenerate hKNondegenerate, ?_⟩
  intro c
  let : SecondCountableTopology F := TestSpaceAnalysis.Construction.localField_secondCountable F hF
  exact ⟨GroupTopology.Construction.circleExtension_isTopologicalGroup hF hEmbedding σ H K c ψ,
    Weak.Construction.circleScalar_continuous σ H K c ψ, LocalTest.Construction.circleScalar_injective F hF σ H K c ψ⟩

theorem oscillator_realization
    {F E : Type} [NormedField F] [NormedField E] [Algebra F E]
    [CompleteSpace F] [LocallyCompactSpace F] [CharZero F]
    [FiniteDimensional F E] [MeasurableSpace F] [BorelSpace F]
    (hF : ¬ DiscreteTopology F) (hEmbedding : Continuous (algebraMap F E))
    (hQuadratic : Module.finrank F E = 2) (σ : E ≃ₐ[F] E)
    (m n : ℕ) (H : Matrix (Fin m) (Fin m) E) (K : Matrix (Fin n) (Fin n) E)
    (hHermitian : ∀ i j, H j i = σ (H i j))
    (hSkewHermitian : ∀ i j, K j i = -σ (K i j))
    (hHNondegenerate : H.det ≠ 0) (hKNondegenerate : K.det ≠ 0)
    (ψ : AddChar F ℂ) (hc : Continuous (fun x : F => ψ x))
    (hu : ∀ x : F, ‖ψ x‖ = 1) (hn : ∃ x : F, ψ x ≠ 1) :
    Nonempty (Oscillator.Construction.SymplecticFrame σ H K) ∧
    ∀ c : Oscillator.Construction.SymplecticFrame σ H K,
      IsTopologicalGroup (Oscillator.Construction.CircleExtension σ H K c ψ) ∧
      Function.Surjective (Oscillator.Construction.circleProjection σ H K c ψ) ∧
      Continuous (Oscillator.Construction.circleScalar σ H K c ψ) ∧
      Function.Injective (Oscillator.Construction.circleScalar σ H K c ψ) ∧
      (∀ a : Oscillator.Construction.CircleExtension σ H K c ψ,
        Oscillator.Construction.circleProjection σ H K c ψ a = 1 ↔
          ∃ z : Circle, Oscillator.Construction.circleScalar σ H K c ψ z = a) := by
  obtain ⟨hframe, htop⟩ := coordinate_and_topological_realization hF hEmbedding hQuadratic
    σ m n H K hHermitian hSkewHermitian hHNondegenerate hKNondegenerate ψ
  refine ⟨hframe, fun c => ?_⟩
  obtain ⟨ht, hcont, hinj⟩ := htop c
  exact ⟨ht, Surjectivity.Construction.circleProjection_surjective σ H K c hF ψ hc hu hn hQuadratic,
    hcont, hinj, Kernel.Construction.circleProjection_kernel σ H K c ψ hF hc hu hn⟩

theorem local_unitary_dual_pair_splitting_ultra
    {F E : Type} [NormedField F] [NormedField E] [Algebra F E]
    [CompleteSpace F] [LocallyCompactSpace F] [CharZero F]
    [LocallyCompactSpace E] [FiniteDimensional F E] [IsUltrametricDist F]
    [MeasurableSpace F] [BorelSpace F]
    (hF : ¬ DiscreteTopology F) (hE : ¬ DiscreteTopology E)
    (hEmbedding : Continuous (algebraMap F E))
    (hQuadratic : Module.finrank F E = 2) (σ : E ≃ₐ[F] E)
    (hConjugation : ∃ z : E, σ z ≠ z)
    (m n : ℕ) (H : Matrix (Fin m) (Fin m) E) (K : Matrix (Fin n) (Fin n) E)
    (hHermitian : ∀ i j, H j i = σ (H i j))
    (hSkewHermitian : ∀ i j, K j i = -σ (K i j))
    (hHNondegenerate : H.det ≠ 0) (hKNondegenerate : K.det ≠ 0)
    (ψ : AddChar F ℂ) (hc : Continuous (fun x : F => ψ x))
    (hu : ∀ x : F, ‖ψ x‖ = 1) (hn : ∃ x : F, ψ x ≠ 1)
    (characters : Characters.Construction.SplittingCharacters F E m n) :
    Nonempty (Oscillator.Construction.SymplecticFrame σ H K) ∧
    ∀ c : Oscillator.Construction.SymplecticFrame σ H K,
      IsTopologicalGroup (Oscillator.Construction.CircleExtension σ H K c ψ) ∧
      Function.Surjective (Oscillator.Construction.circleProjection σ H K c ψ) ∧
      Continuous (Oscillator.Construction.circleScalar σ H K c ψ) ∧
      Function.Injective (Oscillator.Construction.circleScalar σ H K c ψ) ∧
      (∀ a : Oscillator.Construction.CircleExtension σ H K c ψ,
        Oscillator.Construction.circleProjection σ H K c ψ a = 1 ↔
          ∃ z : Circle, Oscillator.Construction.circleScalar σ H K c ψ z = a) ∧
      ∃ splitting : (DualPair.Construction.unitaryGroup σ H × DualPair.Construction.unitaryGroup σ K) →ₜ* Oscillator.Construction.CircleExtension σ H K c ψ,
        ∀ g, Oscillator.Construction.circleProjection σ H K c ψ (splitting g) = DualPair.Construction.continuousDualPairAction σ H K g := by
  obtain ⟨hframe, hreal⟩ := oscillator_realization hF hEmbedding hQuadratic σ m n H K
    hHermitian hSkewHermitian hHNondegenerate hKNondegenerate ψ hc hu hn
  refine ⟨hframe, fun c => ?_⟩
  obtain ⟨ht, hp, hs, hi, hk⟩ := hreal c
  refine ⟨ht, hp, hs, hi, hk, ?_⟩
  have hH : DualPair.Construction.adjointMatrix σ H = H := by
    ext i j
    exact (hHermitian j i).symm
  have hK : DualPair.Construction.adjointMatrix σ K = -K := by
    ext i j
    change σ (K j i) = -K i j
    rw [hSkewHermitian j i, neg_neg]
  exact UltraFactorSplittings.Construction.ultra_dual_pair_splitting σ H K c hF hE hEmbedding hQuadratic hConjugation
    ψ hc hu hn characters hH hK hHNondegenerate hKNondegenerate

theorem local_unitary_dual_pair_splitting
    (F E : Type)
    [NormedField F] [NormedField E] [Algebra F E]
    [CompleteSpace F] [LocallyCompactSpace F] [CharZero F]
    [CompleteSpace E] [LocallyCompactSpace E]
    [FiniteDimensional F E]
    [MeasurableSpace F] [BorelSpace F]
    (hF : ¬ DiscreteTopology F)
    (hE : ¬ DiscreteTopology E)
    (hEmbedding : Continuous (algebraMap F E))
    (hQuadratic : Module.finrank F E = 2)
    (σ : E ≃ₐ[F] E)
    (hConjugation : ∃ z : E, σ z ≠ z)
    (m n : ℕ)
    (H : Matrix (Fin m) (Fin m) E)
    (K : Matrix (Fin n) (Fin n) E)
    (hHermitian : ∀ i j, H j i = σ (H i j))
    (hSkewHermitian : ∀ i j, K j i = -σ (K i j))
    (hHNondegenerate : H.det ≠ 0)
    (hKNondegenerate : K.det ≠ 0)
    (ψ : AddChar F ℂ)
    (hψContinuous : Continuous (fun x : F => ψ x))
    (hψUnitary : ∀ x : F, ‖ψ x‖ = 1)
    (hψNontrivial : ∃ x : F, ψ x ≠ 1)
    (characters : Characters.Construction.SplittingCharacters F E m n) :
    Nonempty (Oscillator.Construction.SymplecticFrame σ H K) ∧
    ∀ c : Oscillator.Construction.SymplecticFrame σ H K,
      IsTopologicalGroup (Oscillator.Construction.CircleExtension σ H K c ψ) ∧
      Function.Surjective (Oscillator.Construction.circleProjection σ H K c ψ) ∧
      Continuous (Oscillator.Construction.circleScalar σ H K c ψ) ∧
      Function.Injective (Oscillator.Construction.circleScalar σ H K c ψ) ∧
      (∀ a : Oscillator.Construction.CircleExtension σ H K c ψ,
        Oscillator.Construction.circleProjection σ H K c ψ a = 1 ↔
          ∃ z : Circle, Oscillator.Construction.circleScalar σ H K c ψ z = a) ∧
      ∃ splitting : (DualPair.Construction.unitaryGroup σ H × DualPair.Construction.unitaryGroup σ K) →ₜ*
          Oscillator.Construction.CircleExtension σ H K c ψ,
        ∀ g : DualPair.Construction.unitaryGroup σ H × DualPair.Construction.unitaryGroup σ K,
          Oscillator.Construction.circleProjection σ H K c ψ (splitting g) =
            DualPair.Construction.continuousDualPairAction σ H K g := by
  obtain ⟨hframe, hreal⟩ := oscillator_realization hF hEmbedding hQuadratic σ m n H K
    hHermitian hSkewHermitian hHNondegenerate hKNondegenerate ψ hψContinuous hψUnitary hψNontrivial
  refine ⟨hframe, fun c => ?_⟩
  obtain ⟨ht, hp, hs, hi, hk⟩ := hreal c
  refine ⟨ht, hp, hs, hi, hk, ?_⟩
  have hH : DualPair.Construction.adjointMatrix σ H = H := by
    ext i j
    exact (hHermitian j i).symm
  have hK : DualPair.Construction.adjointMatrix σ K = -K := by
    ext i j
    change σ (K j i) = -K i j
    rw [hSkewHermitian j i, neg_neg]
  by_cases h : ∀ k : ℕ, ‖(k : F)‖ ≤ 1
  · let : IsUltrametricDist F :=
      IsUltrametricDist.isUltrametricDist_of_forall_norm_natCast_le_one h
    exact UltraFactorSplittings.Construction.ultra_dual_pair_splitting σ H K c hF hE hEmbedding hQuadratic hConjugation
      ψ hψContinuous hψUnitary hψNontrivial characters hH hK hHNondegenerate hKNondegenerate
  · obtain ⟨e, he, hei⟩ := ArchimedeanBase.Construction.real_equiv_of_unbounded_with_quadratic_extension h hQuadratic
    exact Archimedean.Construction.archimedean_dual_pair_splitting σ H K c hF hE hEmbedding hQuadratic hConjugation
      ψ hψContinuous hψUnitary hψNontrivial characters hH hK hHNondegenerate hKNondegenerate e he hei

end

end OAI.RepresentationTheory.Weil.UnitarySplitting.DualPairSplitting.Construction
