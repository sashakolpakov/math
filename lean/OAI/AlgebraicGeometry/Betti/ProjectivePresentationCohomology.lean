import OAI.AlgebraicGeometry.Betti.ProjectiveComponents
import OAI.AlgebraicTopology.DeRham.Comparison.RationalHodgeClasses

/-! # Projective Presentation Cohomology -/

namespace OAI.AlgebraicGeometry

noncomputable section

/-!
# Hodge classes on all smooth projective presentations

The ordinary cohomology is that of the actual complex-point space. The finite
clopen decomposition into integral components, already proved geometrically,
identifies purity with purity of the actual restrictions. This also defines
the usual local notion on presentations whose components have different
dimensions; no common tangent-space dimension is imposed.
-/

open _root_.CategoryTheory

variable (P : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)

/-- Rational singular cohomology of the actual analytic point space. -/
abbrev Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation.rationalCohomology (n : ℕ) : ModuleCat ℚ :=
  Betti.Scheme.schemeBetti (ModuleCat.of ℚ ℚ) P.toOver n

/-- Complex singular cohomology of the same analytic point space. -/
abbrev Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation.complexCohomology (n : ℕ) : ModuleCat ℂ :=
  Betti.Scheme.schemeBetti (ModuleCat.of ℂ ℂ) P.toOver n

/-- The actual rational-to-complex coefficient map. -/
def Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation.rationalCohomologyInclusion (n : ℕ) :
    P.rationalCohomology n ⟶
      (ModuleCat.restrictScalars (algebraMap ℚ ℂ)).obj (P.complexCohomology n) :=
  Betti.Scheme.schemeBettiRationalInclusion P.toOver n

theorem Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation.rationalCohomologyInclusion_injective (n : ℕ) :
    Function.Injective (P.rationalCohomologyInclusion n) :=
  Betti.Scheme.schemeBettiRationalInclusion_injective P.toOver n

/-- Purity on the actual finite clopen component decomposition. -/
def Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation.pureBettiSubspace (p q : ℕ) : Submodule ℂ (P.complexCohomology (p + q)) :=
  (Submodule.pi Set.univ (fun C : irreducibleComponents P.carrier =>
    (P.componentVariety C).pureBettiSubspace p q)).comap
      (P.componentBettiEquiv (ModuleCat.of ℂ ℂ) (p + q)).toLinearMap

theorem Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation.mem_pureBettiSubspace_iff (p q : ℕ) (a : P.complexCohomology (p + q)) :
    a ∈ P.pureBettiSubspace p q ↔
      ∀ C : irreducibleComponents P.carrier,
        P.componentBettiEquiv (ModuleCat.of ℂ ℂ) (p + q) a C ∈
          (P.componentVariety C).pureBettiSubspace p q := by
  simp only [Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation.pureBettiSubspace, Submodule.mem_comap, LinearEquiv.coe_coe,
    Submodule.mem_pi, Set.mem_univ, true_implies]

/-- A rational Hodge class on a smooth projective complex scheme. -/
def Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation.IsRationalHodgeClass (p : ℕ) (a : P.rationalCohomology (p + p)) : Prop :=
  P.rationalCohomologyInclusion (p + p) a ∈ P.pureBettiSubspace p p

set_option backward.isDefEq.respectTransparency false in
/-- Restriction to the actual integral components detects this condition. -/
theorem Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation.isRationalHodgeClass_iff_components (p : ℕ)
    (a : P.rationalCohomology (p + p)) :
    P.IsRationalHodgeClass p a ↔
      ∀ C : irreducibleComponents P.carrier,
        (P.componentVariety C).IsRationalHodgeClass p
          (P.componentBettiEquiv (ModuleCat.of ℚ ℚ) (p + p) a C) := by
  refine (P.mem_pureBettiSubspace_iff p p
    (P.rationalCohomologyInclusion (p + p) a)).trans ?_
  apply forall_congr'
  intro C
  change (P.componentBettiEquiv (ModuleCat.of ℂ ℂ) (p + p)
    (Betti.Scheme.schemeBettiRationalInclusion P.toOver (p + p) a) C ∈ _) ↔ _
  rw [P.componentBettiEquiv_rationalInclusion]
  rfl

/-- The condition is literally the existence, on each actual clopen
component, of a closed pure form representing its rational restriction. -/
theorem Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation.isRationalHodgeClass_iff_closed_components (p : ℕ)
    (a : P.rationalCohomology (p + p)) :
    P.IsRationalHodgeClass p a ↔
      ∀ C : irreducibleComponents P.carrier,
        ∃ form : Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms (P.componentVariety C).analyticModel
            (P.componentVariety C).analyticSpace (p + p),
          Analysis.DifferentialForms.Manifold.CovectorAction.HasTangentBidegree (P.componentVariety C).analyticModel
            (P.componentVariety C).analyticSpace p p
            (form.val : Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm (P.componentVariety C).analyticModel
              (P.componentVariety C).analyticSpace (p + p)) ∧
          ((P.componentVariety C).deRhamBettiIso (p + p)).hom
              ((P.componentVariety C).deRhamClass (p + p) form) =
            (P.componentVariety C).rationalCohomologyInclusion (p + p)
              (P.componentBettiEquiv (ModuleCat.of ℚ ℚ) (p + p) a C) := by
  rw [P.isRationalHodgeClass_iff_components]
  exact forall_congr' fun C => (P.componentVariety C).isRationalHodgeClass_iff p _

/-- The rational submodule of the actual classes defined above. -/
def Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation.rationalHodgeClasses (p : ℕ) : Submodule ℚ (P.rationalCohomology (p + p)) :=
  (Submodule.pi Set.univ (fun C : irreducibleComponents P.carrier =>
    (P.componentVariety C).rationalHodgeClasses p)).comap
      (P.componentBettiEquiv (ModuleCat.of ℚ ℚ) (p + p)).toLinearMap

@[simp]
theorem Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation.mem_rationalHodgeClasses (p : ℕ) (a : P.rationalCohomology (p + p)) :
    a ∈ P.rationalHodgeClasses p ↔ P.IsRationalHodgeClass p a := by
  simp only [Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation.rationalHodgeClasses, Submodule.mem_comap, LinearEquiv.coe_coe,
    Submodule.mem_pi, Set.mem_univ, true_implies,
    Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.mem_rationalHodgeClasses]
  exact (P.isRationalHodgeClass_iff_components p a).symm

end

end OAI.AlgebraicGeometry
