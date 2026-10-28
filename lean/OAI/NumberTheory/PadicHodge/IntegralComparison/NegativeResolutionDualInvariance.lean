import OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.LocalDualInvariance
import OAI.NumberTheory.PadicHodge.IntegralComparison.NegativeTerms

/-! # Negative Resolution Dual Invariance -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.NegativeResolutionDualInvariance

noncomputable section

/-! Negative-twist resolutions have projective section modules on the
coordinate charts. Their actual identity lifts preserve dual sheaf
cohomology, including lifts obtained from common refinements. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.MvPolynomial Opposite

set_option backward.isDefEq.respectTransparency false

universe u

variable {R : Type u} [CommRing R] [IsNoetherianRing R]
  {σ : Type} [Fintype σ] [LinearOrder σ]

attribute [local instance] MvPolynomial.gradedAlgebra

variable {M : (Proj (homogeneousSubmodule σ R)).Modules} {j : σ} {B : ℕ}

omit [IsNoetherianRing R] [Fintype σ] [LinearOrder σ] in
theorem section_projective (h : NegativeTerms.Above M j B)
    (V : (Proj (homogeneousSubmodule σ R)).Opens) (hV : IsAffineOpen V)
    (i : σ) (hVi : V ≤ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i) :
    Projective ((AffineOpen.InternalHom.sections V hV).obj M) := by
  obtain ⟨r, d, _, ⟨e⟩⟩ := h
  exact Projective.of_iso ((AffineOpen.InternalHom.sections V hV).mapIso e).symm
    (Affine.ProjectiveResolutionTerms.coproduct_projective V hV
      (fun t => AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j (d t))
      (fun t => Affine.ProjectiveResolutionTerms.negative_projective V hV i hVi j (d t)))

variable (M) [M.IsQuasicoherent]
  (K L : ChainComplex (Proj (homogeneousSubmodule σ R)).Modules ℕ)
  (hK : ∀ n, NegativeTerms.Above (K.X n) j B)
  (hL : ∀ n, NegativeTerms.Above (L.X n) j B)
  (εK : K ⟶ (ChainComplex.single₀ _).obj M)
  (εL : L ⟶ (ChainComplex.single₀ _).obj M) [QuasiIso εK] [QuasiIso εL]
  (a : K ⟶ L) (ha : a ≫ εL = εK)

include hK hL ha in
omit [IsNoetherianRing R] [Fintype σ] [LinearOrder σ] in
theorem quasiIso (b : ℕ) (hb : b ≤ B) :
    QuasiIso ((Affine.LocalDualInvariance.functor
      (AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j b)).map a.op) := by
  let (n : ℕ) : (K.X n).IsQuasicoherent := NegativeTerms.quasicoherent (hK n)
  let (n : ℕ) : (L.X n).IsQuasicoherent := NegativeTerms.quasicoherent (hL n)
  let (n : ℕ) : (ArithmeticGeometry.OrdinaryLocus.Openness.SheafHomModule.Construction.sheafHomModule (K.X n)
      (AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j b)).IsQuasicoherent :=
    NegativeTerms.dual_quasicoherent (hK n) b hb
  let (n : ℕ) : (ArithmeticGeometry.OrdinaryLocus.Openness.SheafHomModule.Construction.sheafHomModule (L.X n)
      (AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j b)).IsQuasicoherent :=
    NegativeTerms.dual_quasicoherent (hL n) b hb
  exact Affine.LocalDualInvariance.quasiIso _ M K L εK εL a ha
    (AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCover (R := R) (σ := σ))
    (AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.iSup_coordinateOpenCover_eq_top (R := R) (σ := σ))
    (AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCover_isAffineOpen (R := R))
    (fun i n => section_projective (hK n) _ _ i.down le_rfl)
    (fun i n => section_projective (hL n) _ _ i.down le_rfl)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.NegativeResolutionDualInvariance
