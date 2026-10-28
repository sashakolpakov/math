import OAI.AlgebraicGeometry.Betti.ProjectivePresentationCohomology
import OAI.AlgebraicGeometry.Betti.ProjectiveComponentForms
import OAI.AlgebraicGeometry.Betti.RealizationProjectiveComponentRaw

/-! # Projective Presentation Comparison -/

namespace OAI.AlgebraicGeometry

noncomputable section

/-!
# Canonical de Rham comparison on every smooth projective presentation

The actual componentwise comparison is assembled through the proved
topological decomposition. Forms are actual smooth covector sections on the
original analytic point space, with the tangent model allowed to vary between
its clopen components. All maps below are fixed by their actual component
restrictions and the integration-normalized comparisons on those components.
-/

open _root_.CategoryTheory

variable (P : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)

/-- Genuine de Rham cohomology of the componentwise smooth form complex. -/
abbrev Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation.deRhamCohomology (n : ℕ) : ModuleCat ℂ := P.componentDeRhamCohomology n

/-- The canonical comparison with the ordinary cohomology of the original
complex-point space, using the actual clopen decomposition. -/
def Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation.deRhamBettiEquiv (n : ℕ) : P.deRhamCohomology n ≃ₗ[ℂ] P.complexCohomology n :=
  (P.componentDeRhamCohomologyEquiv n).trans
    ((LinearEquiv.piCongrRight fun C : irreducibleComponents P.carrier =>
      ((P.componentVariety C).deRhamBettiIso n).toLinearEquiv).trans
        (P.componentBettiEquiv (ModuleCat.of ℂ ℂ) n).symm)

/-- The same canonical comparison as an isomorphism of complex modules. -/
def Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation.deRhamBettiIso (n : ℕ) : P.deRhamCohomology n ≅ P.complexCohomology n :=
  (P.deRhamBettiEquiv n).toModuleIso

/-- Every actual component restriction is the previously proved
integration-normalized de Rham comparison. -/
theorem Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation.componentBettiEquiv_deRhamBetti (n : ℕ) (a : P.deRhamCohomology n)
    (C : irreducibleComponents P.carrier) :
    P.componentBettiEquiv (ModuleCat.of ℂ ℂ) n (P.deRhamBettiEquiv n a) C =
      ((P.componentVariety C).deRhamBettiIso n).hom
        (P.componentDeRhamCohomologyEquiv n a C) := by
  change (P.componentBettiEquiv (ModuleCat.of ℂ ℂ) n)
    ((P.componentBettiEquiv (ModuleCat.of ℂ ℂ) n).symm _) C = _
  rw [LinearEquiv.apply_symm_apply]
  rfl

/-- The component integration formula determines the global comparison. -/
theorem Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation.deRhamBettiEquiv_unique (n : ℕ)
    (f : P.deRhamCohomology n →ₗ[ℂ] P.complexCohomology n)
    (hf : ∀ a C,
      P.componentBettiEquiv (ModuleCat.of ℂ ℂ) n (f a) C =
        ((P.componentVariety C).deRhamBettiIso n).hom
          (P.componentDeRhamCohomologyEquiv n a C)) :
    f = (P.deRhamBettiEquiv n).toLinearMap := by
  ext a
  apply (P.componentBettiEquiv (ModuleCat.of ℂ ℂ) n).injective
  funext C
  exact (hf a C).trans (P.componentBettiEquiv_deRhamBetti n a C).symm

/-- The usual class of a closed family, now in ordinary complex singular cohomology. -/
def Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation.closedFormBettiClass (n : ℕ) :
    P.componentClosedForms n →ₗ[ℂ] P.complexCohomology n :=
  (P.deRhamBettiEquiv n).toLinearMap.comp (P.componentDeRhamClass n)

theorem Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation.componentBettiEquiv_closedFormBettiClass (n : ℕ)
    (form : P.componentClosedForms n) (C : irreducibleComponents P.carrier) :
    P.componentBettiEquiv (ModuleCat.of ℂ ℂ) n (P.closedFormBettiClass n form) C =
      ((P.componentVariety C).deRhamBettiIso n).hom
        ((P.componentVariety C).deRhamClass n (P.componentClosedFormsEquiv n form C)) := by
  change P.componentBettiEquiv (ModuleCat.of ℂ ℂ) n
    (P.deRhamBettiEquiv n (P.componentDeRhamClass n form)) C = _
  rw [P.componentBettiEquiv_deRhamBetti, P.componentDeRhamCohomologyEquiv_class]

/-- The componentwise Betti purity predicate is exactly the image of the
actual closed-pure-form subspace under the canonical comparison. -/
theorem Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation.deRhamBettiEquiv_mem_pureBettiSubspace_iff (p q : ℕ)
    (a : P.deRhamCohomology (p + q)) :
    P.deRhamBettiEquiv (p + q) a ∈ P.pureBettiSubspace p q ↔
      a ∈ P.componentPureDeRhamSubspace p q := by
  rw [P.mem_pureBettiSubspace_iff, P.mem_componentPureDeRhamSubspace_iff_components]
  apply forall_congr'
  intro C
  rw [P.componentBettiEquiv_deRhamBetti]
  change (∃ b, b ∈ (P.componentVariety C).pureDeRhamSubspace p q ∧
    ((P.componentVariety C).deRhamBettiIso (p + q)).hom b =
      ((P.componentVariety C).deRhamBettiIso (p + q)).hom
        (P.componentDeRhamCohomologyEquiv (p + q) a C)) ↔ _
  constructor
  · rintro ⟨b, hb, he⟩
    have heq := ((P.componentVariety C).deRhamBettiIso (p + q)).toLinearEquiv.injective he
    exact heq ▸ hb
  · intro ha
    exact ⟨_, ha, rfl⟩

/-- Equality of the actual pure subspaces, rather than an assumed
identification of abstract Hodge structures. -/
theorem Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation.pureBettiSubspace_eq_deRhamImage (p q : ℕ) :
    P.pureBettiSubspace p q = (P.componentPureDeRhamSubspace p q).map
      (P.deRhamBettiEquiv (p + q)).toLinearMap := by
  ext b
  constructor
  · intro hb
    refine ⟨(P.deRhamBettiEquiv (p + q)).symm b, ?_,
      (P.deRhamBettiEquiv (p + q)).apply_symm_apply b⟩
    apply (P.deRhamBettiEquiv_mem_pureBettiSubspace_iff p q _).mp
    simpa only [LinearEquiv.apply_symm_apply] using hb
  · rintro ⟨a, ha, rfl⟩
    exact (P.deRhamBettiEquiv_mem_pureBettiSubspace_iff p q a).mpr ha

set_option backward.isDefEq.respectTransparency false in
/-- On an arbitrary smooth projective presentation, a rational Hodge class
has exactly the intended closed pure covector-section representative. -/
theorem Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation.isRationalHodgeClass_iff_closed_form (p : ℕ)
    (a : P.rationalCohomology (p + p)) :
    P.IsRationalHodgeClass p a ↔
      ∃ form : P.componentClosedForms (p + p),
        form ∈ P.componentPureClosedForms p p ∧
        P.closedFormBettiClass (p + p) form = P.rationalCohomologyInclusion (p + p) a := by
  change P.rationalCohomologyInclusion (p + p) a ∈ P.pureBettiSubspace p p ↔ _
  rw [P.pureBettiSubspace_eq_deRhamImage]
  constructor
  · rintro ⟨b, ⟨form, hpure, hform⟩, hb⟩
    refine ⟨form, hpure, ?_⟩
    exact (congrArg (P.deRhamBettiEquiv (p + p)) hform).trans hb
  · rintro ⟨form, hpure, hform⟩
    exact ⟨P.componentDeRhamClass (p + p) form, ⟨form, hpure, rfl⟩, hform⟩

end

end OAI.AlgebraicGeometry
