import Mathlib

/-! # Resolution Cycles -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Augmented.ResolutionCycles

noncomputable section

/-!
# IntegralComparison: canonical cycle short exact sequences of an augmented resolution
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v

variable {C : Type u} [Category.{v} C] [Abelian C]
  (K : CochainComplex C ℕ) {Z : C} (ι : (CochainComplex.single₀ C).obj Z ⟶ K)

abbrev augmentation : Z ⟶ K.X 0 := ι.f 0

theorem augmentation_condition : augmentation K ι ≫ K.d 0 1 = 0 :=
  ((CochainComplex.fromSingle₀Equiv K Z) ι).property

abbrev differentialSequence (n : ℕ) : ShortComplex C :=
  ShortComplex.mk (K.d n (n + 1)) (K.d (n + 1) (n + 2)) (K.d_comp_d n (n + 1) (n + 2))

abbrev initialSequence : ShortComplex C :=
  let T := differentialSequence K 0
  ShortComplex.mk (augmentation K ι) T.toCycles (by
    rw [← cancel_mono T.iCycles, Category.assoc, T.toCycles_i, zero_comp]
    exact augmentation_condition K ι)

abbrev successiveSequence (n : ℕ) : ShortComplex C :=
  let T := differentialSequence K n
  let T' := differentialSequence K (n + 1)
  ShortComplex.mk T.iCycles T'.toCycles (by
    rw [← cancel_mono T'.iCycles, Category.assoc, T'.toCycles_i, zero_comp]
    exact T.iCycles_g)

variable [QuasiIso ι]

theorem augmentation_exact_and_mono :
    (ShortComplex.mk (augmentation K ι) (K.d 0 1) (augmentation_condition K ι)).Exact ∧ Mono (augmentation K ι) := by
  have h := (CochainComplex.quasiIsoAt₀_iff ι).mp (inferInstance : QuasiIsoAt ι 0)
  rw [ShortComplex.quasiIso_iff_of_zeros] at h
  · exact h
  all_goals first | rfl | exact K.shape 0 0 (by simp)

include ι in
theorem positive_exact (n : ℕ) : (differentialSequence K n).Exact := by
  have h : K.ExactAt (n + 1) :=
    (quasiIsoAt_iff_exactAt ι (n + 1) (CochainComplex.exactAt_succ_single_obj _ _)).mp inferInstance
  exact (K.exactAt_iff' n (n + 1) (n + 2) (by simp) (by simp)).mp h

theorem initialSequence_shortExact : (initialSequence K ι).ShortExact := by
  let T := differentialSequence K 0
  let A := initialSequence K ι
  have haug := augmentation_exact_and_mono K ι
  let : Mono (augmentation K ι) := haug.2
  have hker : IsLimit (KernelFork.ofι A.f A.zero) :=
    isKernelOfComp T.iCycles T.f haug.1.fIsKernel A.zero T.toCycles_i
  have hA : A.Exact := ShortComplex.exact_of_f_is_kernel A hker
  let : Epi A.g := (positive_exact K ι 0).epi_toCycles
  exact { exact := hA }

include ι in
theorem successiveSequence_shortExact (n : ℕ) : (successiveSequence K n).ShortExact := by
  let T := differentialSequence K n
  let T' := differentialSequence K (n + 1)
  let A := successiveSequence K n
  have hker : IsLimit (KernelFork.ofι A.f A.zero) :=
    isKernelOfComp T'.iCycles T'.f T.cyclesIsKernel A.zero T'.toCycles_i
  have hA : A.Exact := ShortComplex.exact_of_f_is_kernel A hker
  let : Epi A.g := (positive_exact K ι (n + 1)).epi_toCycles
  exact { exact := hA }

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Augmented.ResolutionCycles
