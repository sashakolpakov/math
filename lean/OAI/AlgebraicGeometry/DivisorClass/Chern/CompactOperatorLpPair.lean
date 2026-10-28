import OAI.AlgebraicGeometry.DivisorClass.Chern.Compact.Adjoint

/-! # Compact Operator Lp Pair -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.CompactOperatorLpPair

noncomputable section

section

/-! A constructed coefficient cutoff equal to one on the test support gives the exact native adjoint L² pairing. -/

open _root_.MeasureTheory
open scoped ContDiff SchwartzMap

theorem compactAdjointSchwartz_L2_pair_of_cutoff {E F G : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    [NormedAddCommGroup G] [InnerProductSpace ℝ G] [CompleteSpace G]
    (A : E → F →L[ℝ] G) (q : 𝓢(E, G)) {U : Set E}
    (hU : IsOpen U) (hA : ContDiffOn ℝ ∞ A U) (hq : HasCompactSupport q) (hs : tsupport q ⊆ U)
    (η : E → ℝ) (hη : ∀ x ∈ tsupport q, η x = 1)
    (a : Lp F 2 (volume : Measure E)) (b : Lp G 2 (volume : Measure E))
    (hab : ∀ᵐ x ∂(volume : Measure E), b x = η x • A x (a x)) :
    inner ℝ a ((Compact.Adjoint.compactAdjointSchwartz A q hU hA hq hs).toLp 2 volume) = inner ℝ b (q.toLp 2 volume) :=
  Compact.Adjoint.compactAdjointSchwartz_L2_pair A q hU hA hq hs a b (hab.mono (fun x hx hqx =>
    hx.trans ((congrArg (fun r : ℝ => r • A x (a x)) (hη x hqx)).trans (one_smul ℝ (A x (a x))))))

end

/-! A compact original coefficient test moves to its actual adjoint coefficient on the L² source. -/

open _root_.MeasureTheory
open scoped ContDiff SchwartzMap

variable {E F G : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G] [CompleteSpace G]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem compactOperatorSchwartz_eq_adjoint (A : E → F →L[ℝ] G) (q : 𝓢(E, F))
    {U : Set E} (hU : IsOpen U) (hA : ContDiffOn ℝ ∞ A U)
    (hq : HasCompactSupport q) (hs : tsupport q ⊆ U) :
    Compact.Adjoint.compactOperatorSchwartz A q hU hA hq hs =
      Compact.Adjoint.compactAdjointSchwartz (fun x => (A x).adjoint) q hU (Compact.Adjoint.coefficient_adjoint_smooth A hA) hq hs := by
  ext x
  simp only [Compact.Adjoint.compactOperatorSchwartz_apply, Compact.Adjoint.compactAdjointSchwartz_apply,
    ContinuousLinearMap.adjoint_adjoint]

theorem compactOperatorSchwartz_L2_pair_of_cutoff (A : E → F →L[ℝ] G) (q : 𝓢(E, F))
    {U : Set E} (hU : IsOpen U) (hA : ContDiffOn ℝ ∞ A U)
    (hq : HasCompactSupport q) (hs : tsupport q ⊆ U)
    (η : E → ℝ) (hη : ∀ x ∈ tsupport q, η x = 1)
    (a : Lp G 2 (volume : Measure E)) (b : Lp F 2 (volume : Measure E))
    (hab : ∀ᵐ x ∂(volume : Measure E), b x = η x • (A x).adjoint (a x)) :
    inner ℝ a ((Compact.Adjoint.compactOperatorSchwartz A q hU hA hq hs).toLp 2 volume) = inner ℝ b (q.toLp 2 volume) :=
  (congrArg (fun t : 𝓢(E, G) => inner ℝ a (t.toLp 2 volume))
    (compactOperatorSchwartz_eq_adjoint A q hU hA hq hs)).trans
    (compactAdjointSchwartz_L2_pair_of_cutoff (fun x => (A x).adjoint) q hU
      (Compact.Adjoint.coefficient_adjoint_smooth A hA) hq hs η hη a b hab)

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.CompactOperatorLpPair
