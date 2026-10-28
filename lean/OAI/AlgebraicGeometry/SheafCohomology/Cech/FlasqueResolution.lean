import OAI.AlgebraicGeometry.SheafCohomology.Cech.FlasqueProducts
import OAI.AlgebraicGeometry.SheafCohomology.Cech.Resolution

/-! # Flasque Resolution -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Cech.FlasqueResolution.TopCat.Sheaf

noncomputable section

open _root_.TopCat
open _root_.TopCat.Sheaf

/-! Flasque cycle sheaves and section lifting in every positive Čech degree. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite

universe u

variable {X : TopCat.{u}} (F : Sheaf AddCommGrpCat.{u} X)
    {ι : Type u} (U : ι → Opens X)

/-- The two consecutive Čech differentials starting in degree `n`. -/
abbrev cechDifferentialShortComplex (n : ℕ) :
    ShortComplex (Sheaf AddCommGrpCat.{u} X) :=
  ShortComplex.mk (SheafDifferential.TopCat.Sheaf.cechDifferential F U n) (SheafDifferential.TopCat.Sheaf.cechDifferential F U (n + 1))
    (SheafComplex.TopCat.Sheaf.cechDifferential_comp F U n)

private abbrev cechInitialCycleSequence :
    ShortComplex (Sheaf AddCommGrpCat.{u} X) :=
  let T := cechDifferentialShortComplex F U 0
  ShortComplex.mk (Augmentation.TopCat.Sheaf.cechAugmentation F U) T.toCycles (by
    rw [← cancel_mono T.iCycles, Category.assoc, T.toCycles_i, zero_comp,
      Augmentation.TopCat.Sheaf.cechAugmentation_comp])

private theorem cechInitialCycleSequence_shortExact (hU : ⨆ i, U i = ⊤) :
    (cechInitialCycleSequence F U).ShortExact := by
  let T := cechDifferentialShortComplex F U 0
  let A := cechInitialCycleSequence F U
  let B := Augmentation.TopCat.Sheaf.cechAugmentedShortComplex F U
  have hB : B.Exact := ZeroExact.TopCat.Sheaf.cechAugmentedShortComplex_exact F U hU
  have : Mono A.f := Resolution.TopCat.Sheaf.cechAugmentation_mono F U hU
  have : Mono B.f := Resolution.TopCat.Sheaf.cechAugmentation_mono F U hU
  have hker : IsLimit (KernelFork.ofι A.f A.zero) :=
    isKernelOfComp T.iCycles T.f hB.fIsKernel A.zero T.toCycles_i
  have hA : A.Exact := ShortComplex.exact_of_f_is_kernel A hker
  have hT : T.Exact := PositiveExact.TopCat.Sheaf.cechShortComplex_exact F U hU 0
  have : Epi A.g := hT.epi_toCycles
  exact { exact := hA }

/-- Successive cycle sheaves, with the intervening Čech term. -/
abbrev cechSuccessiveCycleSequence (n : ℕ) :
    ShortComplex (Sheaf AddCommGrpCat.{u} X) :=
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
  have hT' : T'.Exact := PositiveExact.TopCat.Sheaf.cechShortComplex_exact F U hU (n + 1)
  have : Epi A.g := hT'.epi_toCycles
  exact { exact := hA }

/-- All positive cycle sheaves of the Čech resolution of a flasque sheaf are flasque. -/
theorem cechPositiveCycles_isFlasque [IsFlasque F]
    (hU : ⨆ i, U i = ⊤) (n : ℕ) :
    IsFlasque (cechDifferentialShortComplex F U n).cycles := by
  induction n with
  | zero =>
      have : IsFlasque (Terms.TopCat.Sheaf.cechTerm F U 0) := FlasqueProducts.TopCat.Sheaf.cechTerm_isFlasque F U 0
      exact IsFlasque.of_shortExact_of_isFlasque₁₂
        (cechInitialCycleSequence_shortExact F U hU)
  | succ n ih =>
      have : IsFlasque (cechDifferentialShortComplex F U n).cycles := ih
      have : IsFlasque (Terms.TopCat.Sheaf.cechTerm F U (n + 1)) := FlasqueProducts.TopCat.Sheaf.cechTerm_isFlasque F U (n + 1)
      exact IsFlasque.of_shortExact_of_isFlasque₁₂
        (cechSuccessiveCycleSequence_shortExact F U hU n)

/-- Čech boundaries lift on every open set when the original sheaf is flasque. -/
theorem cechSections_exact_succ [IsFlasque F]
    (hU : ⨆ i, U i = ⊤) (n : ℕ) (V : Opens X)
    (x : (Terms.TopCat.Sheaf.cechTerm F U (n + 1)).obj.obj (op V))
    (hx : (SheafDifferential.TopCat.Sheaf.cechDifferential F U (n + 1)).hom.app (op V) x = 0) :
    ∃ y : (Terms.TopCat.Sheaf.cechTerm F U n).obj.obj (op V),
      (SheafDifferential.TopCat.Sheaf.cechDifferential F U n).hom.app (op V) y = x := by
  let T := cechDifferentialShortComplex F U n
  let K := ShortComplex.mk T.iCycles T.g T.iCycles_g
  have hK : K.Exact := ShortComplex.exact_of_f_is_kernel K T.cyclesIsKernel
  obtain ⟨z, hz⟩ := Sheaf.sections_exact_of_left_exact hK (inferInstance : Mono K.f) x hx
  have : Epi (T.toCycles.hom.app (op V)) := by
    cases n with
    | zero =>
        exact IsFlasque.epi_of_shortExact (cechInitialCycleSequence_shortExact F U hU)
    | succ n =>
        have : IsFlasque (cechDifferentialShortComplex F U n).cycles :=
          cechPositiveCycles_isFlasque F U hU n
        exact IsFlasque.epi_of_shortExact
          (cechSuccessiveCycleSequence_shortExact F U hU n)
  obtain ⟨y, hy⟩ := (AddCommGrpCat.epi_iff_surjective _).mp
    (inferInstance : Epi (T.toCycles.hom.app (op V))) z
  refine ⟨y, ?_⟩
  calc
    T.f.hom.app (op V) y = (T.toCycles ≫ T.iCycles).hom.app (op V) y := by
      rw [T.toCycles_i]
    _ = T.iCycles.hom.app (op V) (T.toCycles.hom.app (op V) y) := rfl
    _ = T.iCycles.hom.app (op V) z := congrArg _ hy
    _ = x := hz

end

end OAI.AlgebraicGeometry.SheafCohomology.Cech.FlasqueResolution.TopCat.Sheaf
