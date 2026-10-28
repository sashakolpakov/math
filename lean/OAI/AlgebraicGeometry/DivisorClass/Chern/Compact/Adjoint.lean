import OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicFrame.Schwartz

/-! # Adjoint -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Compact.Adjoint

noncomputable section

section

/-! Applying a locally smooth coefficient to a compact test supported in its chart gives a genuine global Schwartz function. -/

open Filter
open scoped ContDiff SchwartzMap _root_.Topology

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

omit [NormedSpace ℝ E] in
theorem operator_apply_tsupport (A : E → F →L[ℝ] G) (f : E → F) :
    tsupport (fun x => A x (f x)) ⊆ tsupport f := by
  apply closure_mono
  intro x hx hzero
  apply hx
  change A x (f x) = 0
  rw [hzero, map_zero]

theorem compact_operator_apply_smooth (A : E → F →L[ℝ] G) (f : E → F)
    {U : Set E} (hU : IsOpen U) (hA : ContDiffOn ℝ ∞ A U)
    (hf : ContDiff ℝ ∞ f) (hs : tsupport f ⊆ U) :
    ContDiff ℝ ∞ (fun x => A x (f x)) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hx : x ∈ U
  · exact (hA.clm_apply hf.contDiffOn).contDiffAt (hU.mem_nhds hx)
  · exact contDiffAt_const.congr_of_eventuallyEq (notMem_tsupport_iff_eventuallyEq.mp
      (fun ht => hx (hs (operator_apply_tsupport A f ht))))

omit [NormedSpace ℝ E] in
theorem operator_apply_compact (A : E → F →L[ℝ] G) (f : E → F) (hf : HasCompactSupport f) :
    HasCompactSupport (fun x => A x (f x)) := by
  apply hf.mono
  intro x hx hzero
  apply hx
  change A x (f x) = 0
  rw [hzero, map_zero]

def compactOperatorSchwartz (A : E → F →L[ℝ] G) (f : 𝓢(E, F))
    {U : Set E} (hU : IsOpen U) (hA : ContDiffOn ℝ ∞ A U)
    (hf : HasCompactSupport f) (hs : tsupport f ⊆ U) : 𝓢(E, G) :=
  (operator_apply_compact A f hf).toSchwartzMap (compact_operator_apply_smooth A f hU hA (f.smooth ⊤) hs)

theorem compactOperatorSchwartz_apply (A : E → F →L[ℝ] G) (f : 𝓢(E, F))
    {U : Set E} (hU : IsOpen U) (hA : ContDiffOn ℝ ∞ A U)
    (hf : HasCompactSupport f) (hs : tsupport f ⊆ U) (x : E) :
    compactOperatorSchwartz A f hU hA hf hs x = A x (f x) := rfl

end

section

/-! Compact Schwartz tests for the adjoints of the actual locally smooth coefficient fields. -/

open scoped ContDiff SchwartzMap

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G] [CompleteSpace G]

theorem coefficient_adjoint_smooth {U : Set E} (A : E → F →L[ℝ] G) (hA : ContDiffOn ℝ ∞ A U) :
    ContDiffOn ℝ ∞ (fun z => (A z).adjoint) U :=
  (ContinuousLinearMap.adjoint : (F →L[ℝ] G) ≃ₗᵢ[ℝ] (G →L[ℝ] F)).toContinuousLinearEquiv.contDiff.comp_contDiffOn hA

def compactAdjointSchwartz (A : E → F →L[ℝ] G) (q : 𝓢(E, G))
    {U : Set E} (hU : IsOpen U) (hA : ContDiffOn ℝ ∞ A U)
    (hq : HasCompactSupport q) (hs : tsupport q ⊆ U) : 𝓢(E, F) :=
  compactOperatorSchwartz (fun z => (A z).adjoint) q hU (coefficient_adjoint_smooth A hA) hq hs

theorem compactAdjointSchwartz_apply (A : E → F →L[ℝ] G) (q : 𝓢(E, G))
    {U : Set E} (hU : IsOpen U) (hA : ContDiffOn ℝ ∞ A U)
    (hq : HasCompactSupport q) (hs : tsupport q ⊆ U) (z : E) :
    compactAdjointSchwartz A q hU hA hq hs z = (A z).adjoint (q z) := rfl

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem weak_matrix_pair_adjoint (A : G →L[ℝ] G) (B : F →L[ℝ] G)
    (C : G →L[ℝ] F) (D : F →L[ℝ] F) (a c : F) (v w : G) :
    inner ℝ (A v) w + inner ℝ (B a) w + inner ℝ (C v) c + inner ℝ (D a) c =
      inner ℝ v (A.adjoint w + C.adjoint c) + inner ℝ a (B.adjoint w + D.adjoint c) := by
  simp only [inner_add_right, ContinuousLinearMap.adjoint_inner_right]
  abel

end

/-! An actual coefficient product on the compact test support transfers the adjoint Schwartz pairing to the corresponding original L² source. -/

open _root_.MeasureTheory
open scoped ContDiff SchwartzMap

theorem compactAdjointSchwartz_L2_pair {E F G : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    [NormedAddCommGroup G] [InnerProductSpace ℝ G] [CompleteSpace G]
    (A : E → F →L[ℝ] G) (q : 𝓢(E, G)) {U : Set E}
    (hU : IsOpen U) (hA : ContDiffOn ℝ ∞ A U) (hq : HasCompactSupport q) (hs : tsupport q ⊆ U)
    (a : Lp F 2 (volume : Measure E)) (b : Lp G 2 (volume : Measure E))
    (hab : ∀ᵐ x ∂(volume : Measure E), x ∈ tsupport q → b x = A x (a x)) :
    inner ℝ a ((compactAdjointSchwartz A q hU hA hq hs).toLp 2 volume) = inner ℝ b (q.toLp 2 volume) := by
  rw [L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  apply Filter.Eventually.mono (hab.and
    (((compactAdjointSchwartz A q hU hA hq hs).coeFn_toLp 2 volume).and (q.coeFn_toLp 2 volume)))
  intro x hx
  have ht := (hx.2.1.trans (compactAdjointSchwartz_apply A q hU hA hq hs x))
  have hleft := (congrArg (fun v => inner ℝ (a x) v) ht).trans
    (ContinuousLinearMap.adjoint_inner_right (A x) (a x) (q x))
  have hright := congrArg (fun v => inner ℝ (b x) v) hx.2.2
  by_cases hqx : x ∈ tsupport q
  · exact hleft.trans ((congrArg (fun v => inner ℝ v (q x)) (hx.1 hqx)).symm.trans hright.symm)
  · have hzero : q x = 0 := image_eq_zero_of_notMem_tsupport hqx
    have heq : inner ℝ (A x (a x)) (q x) = inner ℝ (b x) (q x) := by rw [hzero, inner_zero_right, inner_zero_right]
    exact hleft.trans (heq.trans hright.symm)

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Compact.Adjoint
