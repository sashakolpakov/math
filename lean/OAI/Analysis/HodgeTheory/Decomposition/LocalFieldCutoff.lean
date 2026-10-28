import OAI.Analysis.HodgeTheory.Decomposition.CompactFieldSobolev
import OAI.Analysis.HodgeTheory.Decomposition.ComplexOperatorLift

/-! # Local Field Cutoff -/

namespace OAI.Analysis.HodgeTheory.Decomposition.LocalFieldCutoff.Constructions

noncomputable section

section

/-! Smooth real coefficient fields commuting with complex scalars have
genuine smooth complex realizations and preserve native Sobolev regularity. -/

open _root_.MeasureTheory TemperedDistribution
open scoped SchwartzMap ContDiff BigOperators

variable {E F G ι κ : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G] [Fintype ι] [Fintype κ]

def complexFieldProjection (b : OrthonormalBasis κ ℂ F) (c : OrthonormalBasis ι ℂ G)
    (A : E → F →L[ℝ] G) (x : E) : F →L[ℂ] G :=
  ∑ p : ι × κ, inner ℂ (c p.1) (A x (b p.2)) • InnerProductSpace.rankOne ℂ (c p.1) (b p.2)

omit [CompleteSpace F] [CompleteSpace G] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem complexFieldProjection_apply (b : OrthonormalBasis κ ℂ F) (c : OrthonormalBasis ι ℂ G)
    (A : E → F →L[ℝ] G) (x : E)
    (hA : ∀ (r : ℂ) (u : F), A x (r • u) = r • A x u) (u : F) :
    complexFieldProjection b c A x u = A x u := by
  simp only [complexFieldProjection, sum_apply, smul_apply]
  let B : F →L[ℂ] G :=
    { toLinearMap := { toFun := A x, map_add' := (A x).map_add, map_smul' := hA }
      cont := (A x).continuous }
  exact CompactFieldSobolev.Constructions.operator_orthonormal_expansion b c B u

omit [CompleteSpace F] [CompleteSpace G] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] in
theorem complexFieldProjection_smoothOn (b : OrthonormalBasis κ ℂ F) (c : OrthonormalBasis ι ℂ G)
    {A : E → F →L[ℝ] G} {U : Set E} (hA : ContDiffOn ℝ ∞ A U) :
    ContDiffOn ℝ ∞ (complexFieldProjection b c A) U := by
  apply ContDiffOn.sum
  intro p _
  have hev : ContDiffOn ℝ ∞ (fun x => A x (b p.2)) U :=
    (ContinuousLinearMap.apply ℝ G (b p.2)).contDiff.comp_contDiffOn hA
  have hcoeff : ContDiffOn ℝ ∞ (fun x => inner ℂ (c p.1) (A x (b p.2))) U :=
    ((innerSL ℂ (c p.1)).restrictScalars ℝ).contDiff.comp_contDiffOn hev
  exact hcoeff.smul contDiffOn_const

omit [CompleteSpace F] [CompleteSpace G] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem complexFieldProjection_compact (b : OrthonormalBasis κ ℂ F) (c : OrthonormalBasis ι ℂ G)
    {A : E → F →L[ℝ] G} (hA : HasCompactSupport A) : HasCompactSupport (complexFieldProjection b c A) := by
  apply hA.mono
  intro x hx hzero
  apply hx
  simp only [complexFieldProjection, hzero, zero_apply, inner_zero_right, zero_smul, Finset.sum_const_zero]

def compactRealFieldL2 (b : OrthonormalBasis κ ℂ F) (c : OrthonormalBasis ι ℂ G)
    (A : E → F →L[ℝ] G) (hA : ContDiff ℝ ∞ A) (hAc : HasCompactSupport A) :
    Lp F 2 (volume : Measure E) →L[ℂ] Lp G 2 (volume : Measure E) :=
  CompactFieldSobolev.Constructions.compactSmoothFieldL2 b c (complexFieldProjection b c A)
    (contDiffOn_univ.mp (complexFieldProjection_smoothOn b c hA.contDiffOn))
    (complexFieldProjection_compact b c hAc)

omit [CompleteSpace F] [CompleteSpace G] in
theorem compactRealFieldL2_coe (b : OrthonormalBasis κ ℂ F) (c : OrthonormalBasis ι ℂ G)
    (A : E → F →L[ℝ] G) (hA : ContDiff ℝ ∞ A) (hAc : HasCompactSupport A)
    (hℂ : ∀ (x : E) (r : ℂ) (u : F), A x (r • u) = r • A x u)
    (u : Lp F 2 (volume : Measure E)) :
    ∀ᵐ x ∂(volume : Measure E), compactRealFieldL2 b c A hA hAc u x = A x (u x) := by
  have h := CompactFieldSobolev.Constructions.compactSmoothFieldL2_coe b c (complexFieldProjection b c A)
    (contDiffOn_univ.mp (complexFieldProjection_smoothOn b c hA.contDiffOn))
    (complexFieldProjection_compact b c hAc) u
  filter_upwards [h] with x hx
  exact hx.trans (complexFieldProjection_apply b c A x (hℂ x) (u x))

theorem compactRealFieldL2_memSobolev (b : OrthonormalBasis κ ℂ F) (c : OrthonormalBasis ι ℂ G)
    (A : E → F →L[ℝ] G) (hA : ContDiff ℝ ∞ A) (hAc : HasCompactSupport A)
    (n : ℕ) (u : Lp F 2 (volume : Measure E)) (hu : MemSobolev (n : ℝ) 2 (u : 𝓢'(E, F))) :
    MemSobolev (n : ℝ) 2 (compactRealFieldL2 b c A hA hAc u : 𝓢'(E, G)) :=
  CompactFieldSobolev.Constructions.compactSmoothFieldL2_memSobolev b c _ _ _ n u hu

end

/-! Compactly supported cutoff of a locally smooth coefficient field,
including its actual complex linearity and Sobolev action. -/

open _root_.MeasureTheory
open scoped ContDiff _root_.Topology

section Smooth
variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

theorem localFieldCutoff_smooth {U : Set E} (hU : IsOpen U)
    (η : E → ℝ) (hη : ContDiff ℝ ∞ η) (hηU : tsupport η ⊆ U)
    (A : E → G) (hA : ContDiffOn ℝ ∞ A U) : ContDiff ℝ ∞ (fun x => η x • A x) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hx : x ∈ U
  · exact hη.contDiffAt.smul (hA.contDiffAt (hU.mem_nhds hx))
  · have hzero : η =ᶠ[𝓝 x] 0 := notMem_tsupport_iff_eventuallyEq.mp (fun h => hx (hηU h))
    have heq : (fun y => η y • A y) =ᶠ[𝓝 x] (fun _ => (0 : G)) := by
      filter_upwards [hzero] with y hy
      simp only [hy, Pi.zero_apply, zero_smul]
    exact contDiffAt_const.congr_of_eventuallyEq heq

omit [NormedSpace ℝ E] in
theorem localFieldCutoff_compact (η : E → ℝ) (hη : HasCompactSupport η) (A : E → G) :
    HasCompactSupport (fun x => η x • A x) := by
  apply hη.mono
  intro x hx hzero
  apply hx
  change η x • A x = 0
  rw [hzero, zero_smul]

end Smooth

variable {E F G ι κ : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G] [Fintype ι] [Fintype κ]

def localFieldCutoffL2 (b : OrthonormalBasis κ ℂ F) (c : OrthonormalBasis ι ℂ G)
    {U : Set E} (hU : IsOpen U) (η : E → ℝ) (hη : ContDiff ℝ ∞ η)
    (hηc : HasCompactSupport η) (hηU : tsupport η ⊆ U)
    (A : E → F →L[ℝ] G) (hA : ContDiffOn ℝ ∞ A U) :
    Lp F 2 (volume : Measure E) →L[ℂ] Lp G 2 (volume : Measure E) :=
  compactRealFieldL2 b c (fun x => η x • A x)
    (localFieldCutoff_smooth hU η hη hηU A hA) (localFieldCutoff_compact η hηc A)

omit [CompleteSpace F] [CompleteSpace G] in
theorem localFieldCutoffL2_coe (b : OrthonormalBasis κ ℂ F) (c : OrthonormalBasis ι ℂ G)
    {U : Set E} (hU : IsOpen U) (η : E → ℝ) (hη : ContDiff ℝ ∞ η)
    (hηc : HasCompactSupport η) (hηU : tsupport η ⊆ U)
    (A : E → F →L[ℝ] G) (hA : ContDiffOn ℝ ∞ A U)
    (hℂ : ∀ x ∈ U, ∀ (r : ℂ) (u : F), A x (r • u) = r • A x u)
    (u : Lp F 2 (volume : Measure E)) :
    ∀ᵐ x ∂(volume : Measure E), localFieldCutoffL2 b c hU η hη hηc hηU A hA u x = η x • A x (u x) := by
  have hcomplex : ∀ (x : E) (r : ℂ) (v : F),
      (η x • A x) (r • v) = r • (η x • A x) v := by
    intro x r v
    by_cases hx : x ∈ U
    · simp only [smul_apply, hℂ x hx]
      exact smul_comm _ _ _
    · have hzero : η x = 0 := image_eq_zero_of_notMem_tsupport (fun h => hx (hηU h))
      simp only [hzero, zero_smul, zero_apply, smul_zero]
  exact compactRealFieldL2_coe b c _ (localFieldCutoff_smooth hU η hη hηU A hA)
    (localFieldCutoff_compact η hηc A) hcomplex u

theorem localFieldCutoffL2_memSobolev (b : OrthonormalBasis κ ℂ F) (c : OrthonormalBasis ι ℂ G)
    {U : Set E} (hU : IsOpen U) (η : E → ℝ) (hη : ContDiff ℝ ∞ η)
    (hηc : HasCompactSupport η) (hηU : tsupport η ⊆ U)
    (A : E → F →L[ℝ] G) (hA : ContDiffOn ℝ ∞ A U)
    (n : ℕ) (u : Lp F 2 (volume : Measure E))
    (hu : TemperedDistribution.MemSobolev (n : ℝ) 2 (u : TemperedDistribution E F)) :
    TemperedDistribution.MemSobolev (n : ℝ) 2
      (localFieldCutoffL2 b c hU η hη hηc hηU A hA u : TemperedDistribution E G) :=
  compactRealFieldL2_memSobolev b c _ _ _ n u hu

end

end OAI.Analysis.HodgeTheory.Decomposition.LocalFieldCutoff.Constructions
