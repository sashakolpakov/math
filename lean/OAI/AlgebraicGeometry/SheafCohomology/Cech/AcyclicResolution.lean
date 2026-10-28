import OAI.AlgebraicGeometry.SheafCohomology.Cech.Compat
import OAI.AlgebraicGeometry.SheafCohomology.Exact
import Mathlib.Algebra.Homology.ShortComplex.Ab

/-! # Acyclic Resolution -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Cech.AcyclicResolution.Projective

noncomputable section

/-! Global sections of an exact augmented resolution by acyclic sheaves. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite

universe u

variable {X : TopCat.{u}}
    (K : CochainComplex (TopCat.Sheaf AddCommGrpCat.{u} X) ℕ)

/-- The two differentials around a positive degree of a sheaf complex. -/
abbrev resolutionDifferentialShortComplex (n : ℕ) :
    ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X) :=
  ShortComplex.mk (K.d n (n + 1)) (K.d (n + 1) (n + 2))
    (K.d_comp_d n (n + 1) (n + 2))

variable {F : TopCat.Sheaf AddCommGrpCat.{u} X} (e : F ⟶ K.X 0)
    (w : e ≫ K.d 0 1 = 0)

private abbrev initialResolutionCycleSequence :
    ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X) :=
  let T := resolutionDifferentialShortComplex K 0
  ShortComplex.mk e T.toCycles (by
    rw [← cancel_mono T.iCycles, Category.assoc, T.toCycles_i, zero_comp]
    exact w)

private theorem initialResolutionCycleSequence_shortExact [Mono e]
    (haug : (ShortComplex.mk e (K.d 0 1) w).Exact)
    (hpos : ∀ n, (resolutionDifferentialShortComplex K n).Exact) :
    (initialResolutionCycleSequence K e w).ShortExact := by
  let T := resolutionDifferentialShortComplex K 0
  let A := initialResolutionCycleSequence K e w
  have hker : IsLimit (KernelFork.ofι A.f A.zero) :=
    isKernelOfComp T.iCycles T.f haug.fIsKernel A.zero T.toCycles_i
  have hA : A.Exact := ShortComplex.exact_of_f_is_kernel A hker
  have : Epi A.g := (hpos 0).epi_toCycles
  exact { exact := hA }

/-- Consecutive positive cycle sheaves and the intervening resolution term. -/
abbrev successiveResolutionCycleSequence (n : ℕ) :
    ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X) :=
  let T := resolutionDifferentialShortComplex K n
  let T' := resolutionDifferentialShortComplex K (n + 1)
  ShortComplex.mk T.iCycles T'.toCycles (by
    rw [← cancel_mono T'.iCycles, Category.assoc, T'.toCycles_i, zero_comp]
    exact T.iCycles_g)

theorem successiveResolutionCycleSequence_shortExact
    (hpos : ∀ n, (resolutionDifferentialShortComplex K n).Exact) (n : ℕ) :
    (successiveResolutionCycleSequence K n).ShortExact := by
  let T := resolutionDifferentialShortComplex K n
  let T' := resolutionDifferentialShortComplex K (n + 1)
  let A := successiveResolutionCycleSequence K n
  have hker : IsLimit (KernelFork.ofι A.f A.zero) :=
    isKernelOfComp T'.iCycles T'.f T.cyclesIsKernel A.zero T'.toCycles_i
  have hA : A.Exact := ShortComplex.exact_of_f_is_kernel A hker
  have : Epi A.g := (hpos (n + 1)).epi_toCycles
  exact { exact := hA }

set_option backward.isDefEq.respectTransparency false in
/-- Dimension shifting through an actual short exact sequence. -/
theorem cohomology_right_vanish_of_shortExact
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)}
    (hS : S.ShortExact) (n : ℕ)
    (hmiddle : Subsingleton (CategoryTheory.Sheaf.H S.X₂ n))
    (hleft : Subsingleton (CategoryTheory.Sheaf.H S.X₁ (n + 1))) :
    Subsingleton (CategoryTheory.Sheaf.H S.X₃ n) := by
  let : Subsingleton (CategoryTheory.Sheaf.H S.X₂ n) := hmiddle
  let : Subsingleton (CategoryTheory.Sheaf.H S.X₁ (n + 1)) := hleft
  refine subsingleton_of_forall_eq 0 fun c => ?_
  obtain ⟨y, hy⟩ := SheafCohomology.Exact.CategoryTheory.Sheaf.H.longSequence_exact₃_explicit
    hS n (n + 1) rfl c (Subsingleton.elim _ _)
  rw [Subsingleton.elim y 0, map_zero] at hy
  exact hy.symm

/-- Cycles of an exact acyclic augmented resolution are acyclic in positive degrees. -/
theorem resolutionCycles_cohomology_vanish [Mono e]
    (haug : (ShortComplex.mk e (K.d 0 1) w).Exact)
    (hpos : ∀ n, (resolutionDifferentialShortComplex K n).Exact)
    (hF : ∀ q, Subsingleton (CategoryTheory.Sheaf.H F (q + 1)))
    (hK : ∀ p q, Subsingleton (CategoryTheory.Sheaf.H (K.X p) (q + 1)))
    (n q : ℕ) : Subsingleton
      (CategoryTheory.Sheaf.H (resolutionDifferentialShortComplex K n).cycles (q + 1)) := by
  induction n generalizing q with
  | zero =>
      exact cohomology_right_vanish_of_shortExact
        (initialResolutionCycleSequence_shortExact K e w haug hpos) (q + 1)
        (hK 0 q) (hF (q + 1))
  | succ n ih =>
      exact cohomology_right_vanish_of_shortExact
        (successiveResolutionCycleSequence_shortExact K hpos n) (q + 1)
        (hK (n + 1) q) (ih (q + 1))

/-- Global sections of an exact acyclic augmented resolution are exact in every
positive degree. -/
theorem acyclicResolution_sections_exact_succ [Mono e]
    (haug : (ShortComplex.mk e (K.d 0 1) w).Exact)
    (hpos : ∀ n, (resolutionDifferentialShortComplex K n).Exact)
    (hF : ∀ q, Subsingleton (CategoryTheory.Sheaf.H F (q + 1)))
    (hK : ∀ p q, Subsingleton (CategoryTheory.Sheaf.H (K.X p) (q + 1)))
    (n : ℕ) (x : (K.X (n + 1)).obj.obj (op ⊤))
    (hx : (K.d (n + 1) (n + 2)).hom.app (op ⊤) x = 0) :
    ∃ y : (K.X n).obj.obj (op ⊤), (K.d n (n + 1)).hom.app (op ⊤) y = x := by
  let T := resolutionDifferentialShortComplex K n
  let S := ShortComplex.mk T.iCycles T.g T.iCycles_g
  have hS : S.Exact := ShortComplex.exact_of_f_is_kernel S T.cyclesIsKernel
  obtain ⟨z, hz⟩ := TopCat.Sheaf.sections_exact_of_left_exact hS
    (inferInstance : Mono S.f) x hx
  have hsurj : Function.Surjective (T.toCycles.hom.app (op (⊤ : Opens X))) := by
    cases n with
    | zero =>
        have : Subsingleton (CategoryTheory.Sheaf.H F 1) := hF 0
        exact SheafCohomology.Exact.CategoryTheory.Sheaf.H.longSequence_surjective_of_subsingleton_H
          (initialResolutionCycleSequence_shortExact K e w haug hpos) isTerminalTop
    | succ n =>
        have : Subsingleton (CategoryTheory.Sheaf.H
            (resolutionDifferentialShortComplex K n).cycles 1) :=
          resolutionCycles_cohomology_vanish K e w haug hpos hF hK n 0
        exact SheafCohomology.Exact.CategoryTheory.Sheaf.H.longSequence_surjective_of_subsingleton_H
          (successiveResolutionCycleSequence_shortExact K hpos n) isTerminalTop
  obtain ⟨y, hy⟩ := hsurj z
  refine ⟨y, ?_⟩
  calc
    T.f.hom.app (op ⊤) y = (T.toCycles ≫ T.iCycles).hom.app (op ⊤) y := by
      rw [T.toCycles_i]
    _ = T.iCycles.hom.app (op ⊤) (T.toCycles.hom.app (op ⊤) y) := rfl
    _ = T.iCycles.hom.app (op ⊤) z := congrArg _ hy
    _ = x := hz

end

end OAI.AlgebraicGeometry.SheafCohomology.Cech.AcyclicResolution.Projective
