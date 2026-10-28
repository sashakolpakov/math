import OAI.AlgebraicTopology.DeRham.Comparison.ProjectiveIntegration
import OAI.AlgebraicTopology.DeRham.Comparison.Manifold
import OAI.AlgebraicTopology.DeRham.Comparison.SmoothSimplexClass
import OAI.AlgebraicTopology.Cohomology.Singular.GlobalSmoothComparison
import OAI.AlgebraicGeometry.Betti.CohomologySpan

/-! # Projective -/

namespace OAI.AlgebraicTopology.DeRham.Comparison.Projective.IntegralProjectiveVariety

noncomputable section

/-!
# The canonical de Rham comparison for a genuine projective variety

The comparison is the span formed by actual integration over smooth singular
simplices and actual restriction of ordinary singular cochains. Both legs
are proved quasi-isomorphisms. In particular the comparison is not chosen
as an arbitrary isomorphism between two vector spaces.
-/

open _root_.CategoryTheory

/-- Actual integration is a quasi-isomorphism on the compact smooth manifold
derived from the projective variety. -/
instance _root_.OAI.AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.deRhamIntegrationCochain_quasiIso (V : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) :
    QuasiIso V.deRhamIntegrationCochain :=
  Manifold.smoothSimplexIntegrationCochainMap_quasiIso_compact
    V.analyticModel V.analyticSpace

/-- The genuine smooth singular subcomplex computes ordinary singular
cohomology on the derived smooth manifold. -/
instance _root_.OAI.AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.bettiRestrictionCochain_quasiIso (V : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) :
    QuasiIso V.bettiRestrictionCochain :=
  Cohomology.Singular.GlobalSmoothComparison.quasiIso_manifoldSmoothCochainRestriction V.analyticModel V.analyticSpace

/-- The canonical complex de Rham comparison, normalized by actual simplex
integration and the ordinary singular restriction. -/
def _root_.OAI.AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.deRhamBettiIso (V : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (n : ℕ) :
    V.deRhamCohomology n ≅ V.complexCohomology n :=
  AlgebraicGeometry.Betti.CohomologySpan.Realization.cohomologySpanIso V.deRhamIntegrationCochain V.bettiRestrictionCochain n

/-- The defining square says that a form and its Betti class induce the same
class on every genuine smooth singular simplex. -/
theorem _root_.OAI.AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.deRhamBettiIso_hom_comp (V : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (n : ℕ) :
    (V.deRhamBettiIso n).hom ≫ V.bettiToSmoothSingular n =
      V.deRhamToSmoothSingular n :=
  AlgebraicGeometry.Betti.CohomologySpan.Realization.cohomologySpanIso_hom_comp V.deRhamIntegrationCochain
    V.bettiRestrictionCochain n

/-- That square characterizes the comparison uniquely. -/
theorem _root_.OAI.AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.deRhamBettiIso_hom_unique (V : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (n : ℕ)
    (f : V.deRhamCohomology n ⟶ V.complexCohomology n)
    (hf : f ≫ V.bettiToSmoothSingular n = V.deRhamToSmoothSingular n) :
    f = (V.deRhamBettiIso n).hom :=
  AlgebraicGeometry.Betti.CohomologySpan.Realization.cohomologySpanIso_hom_unique V.deRhamIntegrationCochain
    V.bettiRestrictionCochain n f hf

/-- The comparison uses the literal integration cocycle of each closed
form, with the already proved simplex orientation and normalization. -/
theorem _root_.OAI.AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.deRhamToSmoothSingular_formClass (V : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (n : ℕ)
    (form : Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms V.analyticModel V.analyticSpace n) :
    V.deRhamToSmoothSingular n (V.deRhamClass n form) =
      Cohomology.Singular.Representatives.cochainClass V.smoothSingularComplex n
        (SmoothSimplexClass.smoothSimplexIntegrationCocycle
          V.analyticModel V.analyticSpace n form) :=
  SmoothSimplexClass.smoothSimplexIntegrationCohomologyMap_formClass
    V.analyticModel V.analyticSpace n form

/-- Restricting the Betti class of a differential form gives its actual
smooth-singular integration class. -/
theorem _root_.OAI.AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.deRhamBettiIso_formClass (V : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (n : ℕ)
    (form : Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms V.analyticModel V.analyticSpace n) :
    V.bettiToSmoothSingular n ((V.deRhamBettiIso n).hom (V.deRhamClass n form)) =
      Cohomology.Singular.Representatives.cochainClass V.smoothSingularComplex n
        (SmoothSimplexClass.smoothSimplexIntegrationCocycle
          V.analyticModel V.analyticSpace n form) :=
  (ConcreteCategory.congr_hom (V.deRhamBettiIso_hom_comp n)
    (V.deRhamClass n form)).trans (V.deRhamToSmoothSingular_formClass n form)

/-- Equality under comparison is precisely equality of the two actual
smooth-singular classes. -/
theorem _root_.OAI.AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.deRhamBettiIso_apply_eq_iff (V : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (n : ℕ)
    (a : V.deRhamCohomology n) (b : V.complexCohomology n) :
    (V.deRhamBettiIso n).hom a = b ↔
      V.deRhamToSmoothSingular n a = V.bettiToSmoothSingular n b := by
  have hcomp := ConcreteCategory.congr_hom (V.deRhamBettiIso_hom_comp n) a
  have : IsIso (V.bettiToSmoothSingular n) := by
    change IsIso (HomologicalComplex.homologyMap V.bettiRestrictionCochain n)
    infer_instance
  have hinj : Function.Injective (V.bettiToSmoothSingular n) :=
    (asIso (V.bettiToSmoothSingular n)).toLinearEquiv.injective
  constructor
  · intro h
    exact hcomp.symm.trans (congrArg (V.bettiToSmoothSingular n) h)
  · intro h
    apply hinj
    exact hcomp.trans h

/-- The Betti subspace represented by closed forms of the prescribed pure
type, transported through the proved canonical comparison. -/
def _root_.OAI.AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.pureBettiSubspace (V : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (p q : ℕ) :
    Submodule ℂ (V.complexCohomology (p + q)) :=
  (V.pureDeRhamSubspace p q).map (V.deRhamBettiIso (p + q)).hom.hom

/-- Membership in the pure Betti subspace has the literal closed-form
interpretation with the official inverse-character tangent action. -/
theorem _root_.OAI.AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.mem_pureBettiSubspace_iff (V : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (p q : ℕ)
    (a : V.complexCohomology (p + q)) :
    a ∈ V.pureBettiSubspace p q ↔
      ∃ form : Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms V.analyticModel V.analyticSpace (p + q),
        Analysis.DifferentialForms.Manifold.CovectorAction.HasTangentBidegree V.analyticModel V.analyticSpace p q
          (form.val : Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm V.analyticModel V.analyticSpace (p + q)) ∧
        (V.deRhamBettiIso (p + q)).hom (V.deRhamClass (p + q) form) = a := by
  change (∃ b, b ∈ V.pureDeRhamSubspace p q ∧
    (V.deRhamBettiIso (p + q)).hom b = a) ↔ _
  constructor
  · rintro ⟨b, hb, heq⟩
    obtain ⟨form, htype, rfl⟩ := (V.mem_pureDeRhamSubspace_iff p q b).mp hb
    exact ⟨form, htype, heq⟩
  · rintro ⟨form, htype, heq⟩
    exact ⟨V.deRhamClass (p + q) form,
      (V.mem_pureDeRhamSubspace_iff p q _).mpr ⟨form, htype, rfl⟩, heq⟩

/-- A rational class is of Hodge type `(p,p)` when its actual complex
coefficient image is represented by a closed pure `(p,p)` form. -/
def _root_.OAI.AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.IsRationalHodgeClass (V : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (p : ℕ)
    (a : V.rationalCohomology (p + p)) : Prop :=
  V.rationalCohomologyInclusion (p + p) a ∈ V.pureBettiSubspace p p

/-- The rational Hodge condition is explicitly a statement about the real
exterior-derivative kernel, actual complex tangent type, and canonical
singular/de Rham comparison. -/
theorem _root_.OAI.AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.isRationalHodgeClass_iff (V : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (p : ℕ)
    (a : V.rationalCohomology (p + p)) :
    V.IsRationalHodgeClass p a ↔
      ∃ form : Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms V.analyticModel V.analyticSpace (p + p),
        Analysis.DifferentialForms.Manifold.CovectorAction.HasTangentBidegree V.analyticModel V.analyticSpace p p
          (form.val : Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm V.analyticModel V.analyticSpace (p + p)) ∧
        (V.deRhamBettiIso (p + p)).hom (V.deRhamClass (p + p) form) =
          V.rationalCohomologyInclusion (p + p) a :=
  V.mem_pureBettiSubspace_iff p p (V.rationalCohomologyInclusion (p + p) a)

/-- Equivalently, the rational class agrees on smooth singular cohomology
with the actual integration cocycle of a closed pure form. This records
the normalization without an arbitrary comparison isomorphism. -/
theorem _root_.OAI.AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.isRationalHodgeClass_iff_integration (V : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (p : ℕ)
    (a : V.rationalCohomology (p + p)) :
    V.IsRationalHodgeClass p a ↔
      ∃ form : Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms V.analyticModel V.analyticSpace (p + p),
        Analysis.DifferentialForms.Manifold.CovectorAction.HasTangentBidegree V.analyticModel V.analyticSpace p p
          (form.val : Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm V.analyticModel V.analyticSpace (p + p)) ∧
        Cohomology.Singular.Representatives.cochainClass V.smoothSingularComplex (p + p)
          (SmoothSimplexClass.smoothSimplexIntegrationCocycle
            V.analyticModel V.analyticSpace (p + p) form) =
          V.rationalToSmoothSingular (p + p) a := by
  rw [V.isRationalHodgeClass_iff]
  apply exists_congr
  intro form
  apply and_congr_right
  intro _
  refine (V.deRhamBettiIso_apply_eq_iff (p + p) (V.deRhamClass (p + p) form)
    (V.rationalCohomologyInclusion (p + p) a)).trans ?_
  rw [V.deRhamToSmoothSingular_formClass (p + p) form]
  rfl

end

end OAI.AlgebraicTopology.DeRham.Comparison.Projective.IntegralProjectiveVariety
