import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Local.Frames

/-! # Framed Ordinary -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.FramedOrdinary.CM.Ordinary

noncomputable section

/-! Choose the ordinary prime after the actual reference-lattice bound,
retaining the same integral model and every clause of the CMPoints conclusion. -/

open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Local.Frames.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Ordinary.Models.CM

universe u v

theorem ordinary_with_local_frames
    (E : IntermediateField ℚ ℂ) [NumberField E] [IsGalois ℚ E]
    [NumberField.IsCMField E] (K : Type) [Field K] [NumberField K]
    (M : PELModuli.CMPoints.Models.RankThreePELModel E K) (hM : M.HasPrescribedBallPeriods)
    (a : M.Family) (places : GeometricSource.CM.Places E)
    (h_CMPoints : Ordinary.Models.CM.CMPointsInput.{u, v})
    {ι : Type u} [Fintype ι] (L : ι → Type v)
    [∀ i, Field (L i)] [∀ i, NumberField (L i)]
    (excluded : Finset ℕ) (bound : ℕ) :
    ∃ d : ℕ, bound ≤ d ∧
      (∀ (q : ℕ) [Fact q.Prime], d < q → ∀ (j : M.QadicChoice q)
        (v : Fin places.count × Bool),
        Local.Lattice.CM.localLattice
          (Local.Frames.CM.pairedEmbedding E j M.extendedEmbedding places v) (M.datum a).lattice =
          Local.Lattice.CM.standard (q := q)) ∧
      Ordinary.Models.CM.OrdinaryConclusion E K M L excluded d := by
  have hP := (hM.2.2 a).1
  rcases hP with ⟨_, _, _, _, _, _, _, _, _, hΛ, _⟩
  obtain ⟨d, _hd, hframe⟩ := Local.Frames.CM.exists_paired_frame_bound E
    M.extendedEmbedding places (M.datum a).lattice hΛ.1 hΛ.2.1
  refine ⟨max bound d, le_max_left _ _, ?_, h_CMPoints E K M hM L excluded _⟩
  intro q _ hq j v
  exact hframe q (lt_of_le_of_lt (le_max_right _ _) hq) j v

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.FramedOrdinary.CM.Ordinary
