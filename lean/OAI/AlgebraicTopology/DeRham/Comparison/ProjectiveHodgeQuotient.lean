import OAI.AlgebraicTopology.DeRham.Comparison.ManifoldHodgeQuotient
import OAI.AlgebraicTopology.DeRham.Comparison.Projective

/-! # Projective Hodge Quotient -/

namespace OAI.AlgebraicTopology.DeRham.Comparison.ProjectiveHodgeQuotient.IntegralProjectiveVariety

noncomputable section

/-!
# The literal Clay quotient on an actual projective variety

All forms, operators, and comparison maps here are those of the analytically
realized variety. The quotient is closed pure forms modulo the actual image
of d′d″, with zero denominator at either boundary bidegree. Its natural Betti
image is proved equal to the already constructed pure Betti subspace.
-/

/-- The actual closed-pure-form quotient used in the official Clay formulation. -/
abbrev _root_.OAI.AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.clayHodgeQuotient (V : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (p q : ℕ) :=
  ManifoldHodgeQuotient.manifoldHodgeQuotient V.analyticModel V.analyticSpace p q

/-- The natural map from the literal Clay quotient to actual de Rham cohomology. -/
def _root_.OAI.AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.clayHodgeToDeRham (V : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (p q : ℕ) :
    V.clayHodgeQuotient p q →ₗ[ℂ] V.deRhamCohomology (p + q) :=
  ManifoldHodgeQuotient.manifoldHodgeToDeRham V.analyticModel V.analyticSpace p q

/-- Its image is exactly the existing pure de Rham subspace. -/
theorem _root_.OAI.AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.clayHodgeToDeRham_range (V : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (p q : ℕ) :
    LinearMap.range (V.clayHodgeToDeRham p q) = V.pureDeRhamSubspace p q :=
  ManifoldHodgeQuotient.range_manifoldHodgeToDeRham V.analyticModel V.analyticSpace p q

/-- Transport the quotient's natural map by the actual integration-normalized comparison. -/
def _root_.OAI.AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.clayHodgeToBetti (V : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (p q : ℕ) :
    V.clayHodgeQuotient p q →ₗ[ℂ] V.complexCohomology (p + q) :=
  (V.deRhamBettiIso (p + q)).hom.hom.comp (V.clayHodgeToDeRham p q)

/-- The literal quotient image is precisely the pure Betti subspace used in the Hodge condition. -/
theorem _root_.OAI.AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.clayHodgeToBetti_range (V : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (p q : ℕ) :
    LinearMap.range (V.clayHodgeToBetti p q) = V.pureBettiSubspace p q := by
  rw [AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.clayHodgeToBetti, LinearMap.range_comp, AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.clayHodgeToDeRham_range]
  rfl

/-- The quotient map sends an actual closed pure representative to its actual Betti class. -/
theorem _root_.OAI.AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.clayHodgeToBetti_projection (V : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (p q : ℕ)
    (form : ManifoldPureClasses.pureClosedManifoldForms V.analyticModel V.analyticSpace p q) :
    V.clayHodgeToBetti p q
        (ManifoldHodgeQuotient.manifoldHodgeProjection V.analyticModel V.analyticSpace p q form) =
      (V.deRhamBettiIso (p + q)).hom (V.deRhamClass (p + q) form.val) := rfl

/-- Membership in the pure Betti space is exactly representability by the literal Clay quotient. -/
theorem _root_.OAI.AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.mem_pureBettiSubspace_iff_clayHodge (V : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (p q : ℕ)
    (a : V.complexCohomology (p + q)) :
    a ∈ V.pureBettiSubspace p q ↔
      ∃ b : V.clayHodgeQuotient p q, V.clayHodgeToBetti p q b = a := by
  rw [← V.clayHodgeToBetti_range p q]
  rfl

/-- The rational Hodge condition agrees with the actual image of the literal quotient
under rational-to-complex coefficient inclusion. -/
theorem _root_.OAI.AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.isRationalHodgeClass_iff_clayHodge (V : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (p : ℕ)
    (a : V.rationalCohomology (p + p)) :
    V.IsRationalHodgeClass p a ↔
      ∃ b : V.clayHodgeQuotient p p,
        V.clayHodgeToBetti p p b = V.rationalCohomologyInclusion (p + p) a :=
  V.mem_pureBettiSubspace_iff_clayHodge p p (V.rationalCohomologyInclusion (p + p) a)

end

end OAI.AlgebraicTopology.DeRham.Comparison.ProjectiveHodgeQuotient.IntegralProjectiveVariety
