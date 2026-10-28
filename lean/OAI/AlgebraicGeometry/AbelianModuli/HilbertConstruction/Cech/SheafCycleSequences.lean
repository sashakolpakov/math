import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cech.SheafResolution

/-! # Sheaf Cycle Sequences -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cech.SheafCycleSequences.IntrinsicCech

noncomputable section

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite
universe u
variable {X : TopCat.{u}} (F : TopCat.Sheaf AddCommGrpCat.{u} X)
    {ι : Type u} (U : ι → Opens X)

/-- The two consecutive Čech differentials starting in degree `n`. -/
abbrev cechDifferentialShortComplex (n : ℕ) :
    ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X) :=
  ShortComplex.mk (SheafDifferential.IntrinsicCech.cechDifferential F U n) (SheafDifferential.IntrinsicCech.cechDifferential F U (n + 1))
    (IntrinsicCech.SheafComplex.cechDifferential_comp F U n)

abbrev cechInitialCycleSequence :
    ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X) :=
  let T := cechDifferentialShortComplex F U 0
  ShortComplex.mk (SheafAugmentation.IntrinsicCech.cechAugmentation F U) T.toCycles (by
    rw [← cancel_mono T.iCycles, Category.assoc, T.toCycles_i, zero_comp,
      SheafAugmentation.IntrinsicCech.cechAugmentation_comp])

theorem cechInitialCycleSequence_shortExact (hU : ⨆ i, U i = ⊤) :
    (cechInitialCycleSequence F U).ShortExact := by
  let T := cechDifferentialShortComplex F U 0
  let A := cechInitialCycleSequence F U
  let B := SheafAugmentation.IntrinsicCech.cechAugmentedShortComplex F U
  have hB : B.Exact := ZeroCycleStalks.IntrinsicCech.cechAugmentedShortComplex_exact F U hU
  have : Mono A.f := SheafResolution.IntrinsicCech.cechAugmentation_mono F U hU
  have : Mono B.f := SheafResolution.IntrinsicCech.cechAugmentation_mono F U hU
  have hker : IsLimit (KernelFork.ofι A.f A.zero) :=
    isKernelOfComp T.iCycles T.f hB.fIsKernel A.zero T.toCycles_i
  have hA : A.Exact := ShortComplex.exact_of_f_is_kernel A hker
  have hT : T.Exact := PositiveCycleStalks.IntrinsicCech.cechShortComplex_exact F U hU 0
  have : Epi A.g := hT.epi_toCycles
  exact { exact := hA }

/-- Successive cycle sheaves, with the intervening Čech term. -/
abbrev cechSuccessiveCycleSequence (n : ℕ) :
    ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X) :=
  let T := cechDifferentialShortComplex F U n
  let T' := cechDifferentialShortComplex F U (n + 1)
  ShortComplex.mk T.iCycles T'.toCycles (by
    rw [← cancel_mono T'.iCycles, Category.assoc, T'.toCycles_i, zero_comp]
    exact T.iCycles_g)

/-- Exactness of the sheaf Čech resolution gives short exact sequences of cycles. -/
theorem cechSuccessiveCycleSequence_shortExact (hU : ⨆ i, U i = ⊤) (n : ℕ) :
    (cechSuccessiveCycleSequence F U n).ShortExact := by
  let T := cechDifferentialShortComplex F U n
  let T' := cechDifferentialShortComplex F U (n + 1)
  let A := cechSuccessiveCycleSequence F U n
  have hker : IsLimit (KernelFork.ofι A.f A.zero) :=
    isKernelOfComp T'.iCycles T'.f T.cyclesIsKernel A.zero T'.toCycles_i
  have hA : A.Exact := ShortComplex.exact_of_f_is_kernel A hker
  have hT' : T'.Exact := PositiveCycleStalks.IntrinsicCech.cechShortComplex_exact F U hU (n + 1)
  have : Epi A.g := hT'.epi_toCycles
  exact { exact := hA }

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cech.SheafCycleSequences.IntrinsicCech
