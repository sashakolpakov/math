import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cech.SheafCycleSequences
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FlasqueCechSheafTerms

/-! # Flasque Cech Section Exactness -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FlasqueCechSectionExactness.IntrinsicCech

noncomputable section

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite
universe u
variable {X : TopCat.{u}} (F : TopCat.Sheaf AddCommGrpCat.{u} X)
    {ι : Type u} (U : ι → Opens X)

/-- All positive cycle sheaves of the Čech resolution of a flasque sheaf are flasque. -/
theorem cechPositiveCycles_isFlasque [TopCat.Sheaf.IsFlasque F]
    (hU : ⨆ i, U i = ⊤) (n : ℕ) :
    TopCat.Sheaf.IsFlasque (Cech.SheafCycleSequences.IntrinsicCech.cechDifferentialShortComplex F U n).cycles := by
  induction n with
  | zero =>
      have : TopCat.Sheaf.IsFlasque (IntrinsicCech.SheafTerms.cechTerm F U 0) := FlasqueCechSheafTerms.IntrinsicCech.cechTerm_isFlasque F U 0
      exact TopCat.Sheaf.IsFlasque.of_shortExact_of_isFlasque₁₂
        (Cech.SheafCycleSequences.IntrinsicCech.cechInitialCycleSequence_shortExact F U hU)
  | succ n ih =>
      have : TopCat.Sheaf.IsFlasque (Cech.SheafCycleSequences.IntrinsicCech.cechDifferentialShortComplex F U n).cycles := ih
      have : TopCat.Sheaf.IsFlasque (IntrinsicCech.SheafTerms.cechTerm F U (n + 1)) := FlasqueCechSheafTerms.IntrinsicCech.cechTerm_isFlasque F U (n + 1)
      exact TopCat.Sheaf.IsFlasque.of_shortExact_of_isFlasque₁₂
        (Cech.SheafCycleSequences.IntrinsicCech.cechSuccessiveCycleSequence_shortExact F U hU n)

/-- Čech boundaries lift on every open set when the original sheaf is flasque. -/
theorem cechSections_exact_succ [TopCat.Sheaf.IsFlasque F]
    (hU : ⨆ i, U i = ⊤) (n : ℕ) (V : Opens X)
    (x : (IntrinsicCech.SheafTerms.cechTerm F U (n + 1)).obj.obj (op V))
    (hx : (Cech.SheafDifferential.IntrinsicCech.cechDifferential F U (n + 1)).hom.app (op V) x = 0) :
    ∃ y : (IntrinsicCech.SheafTerms.cechTerm F U n).obj.obj (op V),
      (Cech.SheafDifferential.IntrinsicCech.cechDifferential F U n).hom.app (op V) y = x := by
  let T := Cech.SheafCycleSequences.IntrinsicCech.cechDifferentialShortComplex F U n
  let K := ShortComplex.mk T.iCycles T.g T.iCycles_g
  have hK : K.Exact := ShortComplex.exact_of_f_is_kernel K T.cyclesIsKernel
  obtain ⟨z, hz⟩ := TopCat.Sheaf.sections_exact_of_left_exact hK (inferInstance : Mono K.f) x hx
  have : Epi (T.toCycles.hom.app (op V)) := by
    cases n with
    | zero =>
        exact TopCat.Sheaf.IsFlasque.epi_of_shortExact (Cech.SheafCycleSequences.IntrinsicCech.cechInitialCycleSequence_shortExact F U hU)
    | succ n =>
        have : TopCat.Sheaf.IsFlasque (Cech.SheafCycleSequences.IntrinsicCech.cechDifferentialShortComplex F U n).cycles :=
          cechPositiveCycles_isFlasque F U hU n
        exact TopCat.Sheaf.IsFlasque.epi_of_shortExact
          (Cech.SheafCycleSequences.IntrinsicCech.cechSuccessiveCycleSequence_shortExact F U hU n)
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

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FlasqueCechSectionExactness.IntrinsicCech
