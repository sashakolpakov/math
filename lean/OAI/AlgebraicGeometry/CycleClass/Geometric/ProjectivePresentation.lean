import OAI.AlgebraicGeometry.Betti.GeometricClasses
import OAI.AlgebraicGeometry.CycleClass.Geometric.ProjectiveComponentCycles
import OAI.AlgebraicGeometry.Betti.ProjectivePresentationCohomology

/-! # Projective Presentation -/

namespace OAI.AlgebraicGeometry

noncomputable section

/-!
# Geometric cycle classes on every smooth projective presentation

The actual finite clopen decomposition identifies both ordinary cohomology
and finite rational cycles with their component families. The class map below
uses the independently constructed fundamental-cycle trace class on each
integral component. No common dimension or connectedness is assumed.
-/

variable (P : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)

/-- The geometric fundamental-cycle class map, assembled through the
actual component inclusions on cycles and ordinary cohomology. -/
def Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation.geometricCycleClassMap (p : ℕ) :
    P.RationalDimensionCycle p →ₗ[ℚ] P.rationalCohomology (p + p) :=
  (P.componentBettiEquiv (ModuleCat.of ℚ ℚ) (p + p)).symm.toLinearMap.comp
    ((LinearMap.pi fun C : irreducibleComponents P.carrier =>
      ((P.componentVariety C).geometricCycleClassMap p).comp (LinearMap.proj C)).comp
        (P.componentDimensionCycleEquiv p).toLinearMap)

/-- Every component coordinate is the actual geometric class of the
corresponding component cycle. -/
theorem Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation.componentBettiEquiv_geometricCycleClassMap (p : ℕ)
    (z : P.RationalDimensionCycle p) (C : irreducibleComponents P.carrier) :
    P.componentBettiEquiv (ModuleCat.of ℚ ℚ) (p + p) (P.geometricCycleClassMap p z) C =
      (P.componentVariety C).geometricCycleClassMap p
        (P.componentDimensionCycleEquiv p z C) := by
  change (P.componentBettiEquiv (ModuleCat.of ℚ ℚ) (p + p))
    ((P.componentBettiEquiv (ModuleCat.of ℚ ℚ) (p + p)).symm _) C = _
  rw [LinearEquiv.apply_symm_apply]
  rfl

/-- The actual image of finite rational geometric algebraic cycles. -/
def Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation.geometricAlgebraicClasses (p : ℕ) : Submodule ℚ (P.rationalCohomology (p + p)) :=
  LinearMap.range (P.geometricCycleClassMap p)

theorem Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation.mem_geometricAlgebraicClasses_iff (p : ℕ) (a : P.rationalCohomology (p + p)) :
    a ∈ P.geometricAlgebraicClasses p ↔
      ∃ z : P.RationalDimensionCycle p, P.geometricCycleClassMap p z = a := Iff.rfl

/-- Component cycles assemble to a genuine finite cycle, so algebraicity
is equivalent to algebraicity of every actual component restriction. -/
theorem Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation.mem_geometricAlgebraicClasses_iff_components (p : ℕ)
    (a : P.rationalCohomology (p + p)) :
    a ∈ P.geometricAlgebraicClasses p ↔
      ∀ C : irreducibleComponents P.carrier,
        P.componentBettiEquiv (ModuleCat.of ℚ ℚ) (p + p) a C ∈
          (P.componentVariety C).geometricAlgebraicClasses p := by
  constructor
  · rintro ⟨z, rfl⟩ C
    exact ⟨P.componentDimensionCycleEquiv p z C,
      (P.componentBettiEquiv_geometricCycleClassMap p z C).symm⟩
  · intro h
    have hC := fun C : irreducibleComponents P.carrier =>
      ((P.componentVariety C).mem_geometricAlgebraicClasses_iff p _).mp (h C)
    choose z hz using hC
    refine ⟨(P.componentDimensionCycleEquiv p).symm z, ?_⟩
    apply (P.componentBettiEquiv (ModuleCat.of ℚ ℚ) (p + p)).injective
    funext C
    rw [P.componentBettiEquiv_geometricCycleClassMap, LinearEquiv.apply_symm_apply]
    exact hz C

theorem Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation.geometricAlgebraicClasses_eq_comap_components (p : ℕ) :
    P.geometricAlgebraicClasses p =
      (Submodule.pi Set.univ (fun C : irreducibleComponents P.carrier =>
        (P.componentVariety C).geometricAlgebraicClasses p)).comap
          (P.componentBettiEquiv (ModuleCat.of ℚ ℚ) (p + p)).toLinearMap := by
  ext a
  rw [P.mem_geometricAlgebraicClasses_iff_components]
  simp only [Submodule.mem_comap, Submodule.mem_pi, Set.mem_univ, true_implies,
    LinearEquiv.coe_coe]

/-- The universal Hodge containment is detected on the actual components. -/
theorem Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation.rationalHodgeClasses_le_geometricAlgebraicClasses_iff_components (p : ℕ) :
    P.rationalHodgeClasses p ≤ P.geometricAlgebraicClasses p ↔
      ∀ C : irreducibleComponents P.carrier,
        (P.componentVariety C).rationalHodgeClasses p ≤
          (P.componentVariety C).geometricAlgebraicClasses p := by
  classical
  rw [P.geometricAlgebraicClasses_eq_comap_components]
  change (Submodule.pi Set.univ
      (fun C : irreducibleComponents P.carrier =>
        (P.componentVariety C).rationalHodgeClasses p)).comap
        (P.componentBettiEquiv (ModuleCat.of ℚ ℚ) (p + p)).toLinearMap ≤ _ ↔ _
  rw [Submodule.comap_le_comap_iff_of_surjective
    (P.componentBettiEquiv (ModuleCat.of ℚ ℚ) (p + p)).surjective]
  constructor
  · intro h C a ha
    have hs : Pi.single C a ∈ Submodule.pi Set.univ
        (fun D : irreducibleComponents P.carrier =>
          (P.componentVariety D).rationalHodgeClasses p) :=
      Submodule.le_comap_single_pi _ ha
    have ht := h hs C (Set.mem_univ C)
    change (Pi.single C a : ∀ D : irreducibleComponents P.carrier,
      (P.componentVariety D).rationalCohomology (p + p)) C ∈
        (P.componentVariety C).geometricAlgebraicClasses p at ht
    simpa only [Pi.single_eq_same] using ht
  · intro h
    exact Submodule.pi_mono fun C _ => h C

/-- Noncontainment is witnessed by an actual rational Hodge class. -/
theorem Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation.exists_isRationalHodgeClass_not_geometric_algebraic_iff (p : ℕ) :
    (∃ a : P.rationalCohomology (p + p),
      P.IsRationalHodgeClass p a ∧ a ∉ P.geometricAlgebraicClasses p) ↔
      ¬ P.rationalHodgeClasses p ≤ P.geometricAlgebraicClasses p := by
  classical
  simp only [SetLike.le_def, P.mem_rationalHodgeClasses, not_forall, exists_prop]

end

end OAI.AlgebraicGeometry
