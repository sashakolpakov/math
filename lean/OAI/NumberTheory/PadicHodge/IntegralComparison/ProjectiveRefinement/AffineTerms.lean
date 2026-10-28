import OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveRefinement.DualMap

/-! # Affine Terms -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveRefinement.AffineTerms

noncomputable section

/-! Affine projectivity and dual coherence of the original fixed and
common negative resolutions, exposed as opaque proof constants. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.MvPolynomial

universe u
variable {R : Type u} [CommRing R] [IsNoetherianRing R]
  {σ : Type} [Fintype σ] [LinearOrder σ]
attribute [local instance] MvPolynomial.gradedAlgebra
variable (M M' : (Proj (homogeneousSubmodule σ R)).Modules)
  [M.IsQuasicoherent] [M.IsFiniteType] [M'.IsQuasicoherent] [M'.IsFiniteType]
  (j : σ) (B b : ℕ) (hb : b ≤ B) (f : M ⟶ M')

omit [LinearOrder σ] in
theorem fixed_qc (q : ℕ) : ((IntegralComparison.Projective.NegativeResolution.complex M j B).X q).IsQuasicoherent :=
  NegativeTerms.quasicoherent (DualMap.fixed_term_above M j B q)

omit [LinearOrder σ] in
theorem common_qc (q : ℕ) : ((IntegralComparison.Projective.NegativeRefinement.complex M M' j B f).X q).IsQuasicoherent :=
  NegativeTerms.quasicoherent (IntegralComparison.Projective.NegativeRefinement.term_above M M' j B f q)

include hb in
omit [LinearOrder σ] in
theorem fixed_dual_qc (q : ℕ) :
    (ArithmeticGeometry.OrdinaryLocus.Openness.SheafHomModule.Construction.sheafHomModule ((IntegralComparison.Projective.NegativeResolution.complex M j B).X q)
      (AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j b)).IsQuasicoherent :=
  NegativeTerms.dual_quasicoherent (DualMap.fixed_term_above M j B q) b hb

include hb in
omit [LinearOrder σ] in
theorem common_dual_qc (q : ℕ) :
    (ArithmeticGeometry.OrdinaryLocus.Openness.SheafHomModule.Construction.sheafHomModule ((IntegralComparison.Projective.NegativeRefinement.complex M M' j B f).X q)
      (AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j b)).IsQuasicoherent :=
  NegativeTerms.dual_quasicoherent (IntegralComparison.Projective.NegativeRefinement.term_above M M' j B f q) b hb

variable (U : (Proj (homogeneousSubmodule σ R)).Opens) (hU : IsAffineOpen U)
  (k : σ) (hUk : U ≤ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) k)

include k hUk in
omit [LinearOrder σ] in
theorem fixed_projective (q : ℕ) : Projective ((AffineOpen.InternalHom.sections U hU).obj
    ((IntegralComparison.Projective.NegativeResolution.complex M j B).X q)) :=
  NegativeResolutionDualInvariance.section_projective
    (DualMap.fixed_term_above M j B q) U hU k hUk

include k hUk in
omit [LinearOrder σ] in
theorem common_projective (q : ℕ) : Projective ((AffineOpen.InternalHom.sections U hU).obj
    ((IntegralComparison.Projective.NegativeRefinement.complex M M' j B f).X q)) :=
  NegativeResolutionDualInvariance.section_projective
    (IntegralComparison.Projective.NegativeRefinement.term_above M M' j B f q) U hU k hUk

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveRefinement.AffineTerms
