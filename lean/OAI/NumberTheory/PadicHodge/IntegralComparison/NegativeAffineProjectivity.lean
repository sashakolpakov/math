import OAI.NumberTheory.PadicHodge.IntegralComparison.NegativeTerms
import OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.ProjectiveResolutionTerms

/-! # Negative Affine Projectivity -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.NegativeAffineProjectivity

noncomputable section

/-! Every finite sum of negative twists, including the actual common
refinement terms, has projective sections on a coordinate subopen. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.MvPolynomial
set_option backward.isDefEq.respectTransparency false
universe u
variable {R : Type u} [CommRing R] [IsNoetherianRing R]
  {σ : Type} [Fintype σ] [LinearOrder σ]
attribute [local instance] MvPolynomial.gradedAlgebra
variable (U : (Proj (homogeneousSubmodule σ R)).Opens) (hU : IsAffineOpen U)
  (i : σ) (hi : U ≤ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i)
  {M : (Proj (homogeneousSubmodule σ R)).Modules} {j : σ} {B : ℕ}

include i hi in
omit [IsNoetherianRing R] [Fintype σ] [LinearOrder σ] in
theorem of_above (h : NegativeTerms.Above M j B) :
    Projective ((AffineOpen.InternalHom.sections U hU).obj M) := by
  obtain ⟨r, d, _, ⟨e⟩⟩ := h
  exact Projective.of_iso ((AffineOpen.InternalHom.sections U hU).mapIso e).symm
    (Affine.ProjectiveResolutionTerms.coproduct_projective U hU
      (fun a => AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j (d a))
      (fun a => Affine.ProjectiveResolutionTerms.negative_projective U hU i hi j (d a)))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.NegativeAffineProjectivity
