import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Constructed.OrdinaryPrime
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Local.Lattice

/-! # Labeled Local Frames -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.LabeledLocalFrames.CM

noncomputable section

/-! One bound supplies standard local frames for every member of the
actual finite PEL family. The embeddings extend precisely the original
integral characters, before choosing the native ordinary reductions. -/

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Prerequisites OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Neighbor.Counting.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.QadicModelMap.CM

universe u v

variable {E K : Type} [Field E] [NumberField E]
  [NumberField.IsCMField E] [IsGalois ℚ E] [Field K] [NumberField K]
  (M : PELModuli.CMPoints.Models.RankThreePELModel E K)

def embedding {q : ℕ} [Fact q.Prime] (j : M.QadicChoice q) (τ : Gal(E/ℚ)) : E →+* ℚ_[q] :=
  (QadicModelMap.CM.localFieldEmbedding j).comp (M.extendedEmbedding.comp τ.toRingHom)

omit [IsGalois ℚ E] in
theorem embedding_integral {q : ℕ} [Fact q.Prime] (j : M.QadicChoice q)
    (τ : Gal(E/ℚ)) (a : NumberField.RingOfIntegers E) :
    embedding M j τ a = (j.localCharacter M.extendedEmbedding τ a : ℚ_[q]) :=
  (RingHom.congr_fun j.integral_compatibility
    (NumberField.RingOfIntegers.mapRingHom (M.extendedEmbedding.comp τ.toRingHom) a)).symm

def FramesAbove (bound : ℕ) : Prop :=
  ∀ (q : ℕ) [Fact q.Prime], bound < q → ∀ (j : M.QadicChoice q)
    (a : M.Family) (τ : Gal(E/ℚ)),
    Local.Lattice.CM.localLattice (embedding M j τ) (M.datum a).lattice =
      Local.Lattice.CM.standard (q := q)

omit [IsGalois ℚ E] in
theorem uniform_bound (hM : M.HasPrescribedBallPeriods) (bound : ℕ) :
    ∃ d : ℕ, bound ≤ d ∧ FramesAbove M d := by
  classical
  have hframe (a : M.Family) := by
    have hP := (hM.2.2 a).1
    rcases hP with ⟨_, _, _, _, _, _, _, _, _, hΛ, _⟩
    exact Local.Lattice.CM.exists_uniform_local_frame (M.datum a).lattice hΛ.1 hΛ.2.1
  choose d hd hlocal using hframe
  let b := max bound (Finset.univ.sup d)
  refine ⟨b, le_max_left _ _, ?_⟩
  intro q _ hq j a τ
  have hda : d a < q := lt_of_le_of_lt
    ((Finset.le_sup (f := d) (Finset.mem_univ a)).trans (le_max_right _ _)) hq
  exact hlocal a q (Nat.coprime_of_lt_prime (hd a).ne' hda (Fact.out : q.Prime))
    (embedding M j τ) (j.localCharacter M.extendedEmbedding τ) (embedding_integral M j τ)

theorem native_reductions_with_frames
    (hM : M.HasPrescribedBallPeriods)
    (hNeighborCounting : Neighbor.Counting.CM.NeighborCountingInput) (hFrobeniusKernel : Isogenies.NeighborCounting.Prerequisites.FullFrobeniusKernelInput)
    (hCMPoints : AbelianScheme.FrobeniusKernel.CMPoints.Construction.CMPointsInput.{u, v}) (hCartierDuality : AbelianScheme.FrobeniusKernel.CartierDuality.Construction.FullCartierDualityInput.{0}) (hTorsionQuotient : AbelianScheme.IsogenyQuotient.Unit.Construction.TorsionQuotientInput.{0})
    {I : Type u} [Fintype I] (fields : I → Type v)
    [∀ i, Field (fields i)] [∀ i, NumberField (fields i)]
    (excluded : Finset ℕ) (bound : ℕ) :
    ∃ d : ℕ, bound ≤ d ∧ FramesAbove M d ∧
      Constructed.OrdinaryPrime.CM.Ordinary.Conclusion hTorsionQuotient E K M hM fields excluded d := by
  obtain ⟨d, hd, hframes⟩ := uniform_bound M hM bound
  exact ⟨d, hd, hframes, Constructed.OrdinaryPrime.CM.Ordinary.exists_prime
    hNeighborCounting hFrobeniusKernel hCMPoints hCartierDuality hTorsionQuotient E K M hM fields excluded d⟩

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.LabeledLocalFrames.CM
