import OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.InternalHomCoherence
import OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.InternalHomVanishing
import OAI.NumberTheory.PadicHodge.IntegralComparison.Module.FiniteTypeQuotient

/-! # Negative Terms -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.NegativeTerms

noncomputable section

/-! Intrinsic properties of finite sums of negative twists, applicable
to both chosen resolutions and their common refinements. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.MvPolynomial Opposite

set_option backward.isDefEq.respectTransparency false

universe u

variable {R : Type u} [CommRing R] [IsNoetherianRing R]
  {σ : Type} [Fintype σ] [LinearOrder σ]

attribute [local instance] MvPolynomial.gradedAlgebra

def Above (M : (Proj (homogeneousSubmodule σ R)).Modules) (j : σ) (B : ℕ) : Prop :=
  ∃ r : ℕ, ∃ d : Fin r → ℕ, (∀ i, B ≤ d i) ∧
    Nonempty (M ≅ ∐ fun i => AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j (d i))

variable {M : (Proj (homogeneousSubmodule σ R)).Modules} {j : σ} {B : ℕ}

omit [IsNoetherianRing R] [Fintype σ] [LinearOrder σ] in
theorem presentation (P : Projective.NegativeResolution.Presentation M j B) :
    Above P.source j B := ⟨P.count, P.degree, P.degree_bound, ⟨Iso.refl _⟩⟩

omit [IsNoetherianRing R] [Fintype σ] [LinearOrder σ] in
theorem quasicoherent (h : Above M j B) : M.IsQuasicoherent := by
  obtain ⟨r, d, _, ⟨e⟩⟩ := h
  exact (AlgebraicGeometry.SheafCohomology.Projective.Quasicoherent.Scheme.Modules.isQuasicoherent _).prop_of_iso e.symm
    (AlgebraicGeometry.SheafCohomology.Projective.TwoStagePresentation.MvPolynomial.negativeTwistCoproduct_quasicoherent j d)

omit [IsNoetherianRing R] [Fintype σ] [LinearOrder σ] in
theorem finiteType (h : Above M j B) : M.IsFiniteType := by
  let := quasicoherent h
  obtain ⟨r, d, _, ⟨e⟩⟩ := h
  let := AlgebraicGeometry.SheafCohomology.Projective.TwoStagePresentation.MvPolynomial.negativeTwistCoproduct_quasicoherent (R := R) j d
  let := AlgebraicGeometry.SheafCohomology.Projective.TwoStagePresentation.MvPolynomial.negativeTwistCoproduct_finiteType (R := R) j d
  exact Module.FiniteTypeQuotient.of_epi e.inv

omit [IsNoetherianRing R] in
theorem lower_cohomology_zero [Nontrivial σ] (h : Above M j B) (hB : 0 < B)
    (q : ℕ) (hq : q + 1 ≠ Fintype.card σ) :
    IsZero ((ProjectiveResolution.Vanishing.cohomology (R := R) (σ := σ) q).obj M) := by
  obtain ⟨r, d, hd, ⟨e⟩⟩ := h
  exact (ProjectiveResolution.Vanishing.coproduct_isZero j d
    (fun i => hB.trans_le (hd i)) q hq).of_iso
      ((ProjectiveResolution.Vanishing.cohomology (R := R) (σ := σ) q).mapIso e)

omit [IsNoetherianRing R] [Fintype σ] [LinearOrder σ] in
theorem dual_quasicoherent (h : Above M j B) (b : ℕ) (hb : b ≤ B) :
    (ArithmeticGeometry.OrdinaryLocus.Openness.SheafHomModule.Construction.sheafHomModule M (AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j b)).IsQuasicoherent := by
  obtain ⟨r, d, hd, ⟨e⟩⟩ := h
  let F := SchemeInternalHom.functor (AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j b)
  exact (AlgebraicGeometry.SheafCohomology.Projective.Quasicoherent.Scheme.Modules.isQuasicoherent _).prop_of_iso (F.mapIso e.op)
    (Projective.InternalHomCoherence.coproduct j d b (fun i => hb.trans (hd i)))

omit [IsNoetherianRing R] in
theorem higher_dual_cohomology_zero (h : Above M j B) (b : ℕ) (hb : b ≤ B) (q : ℕ) :
    IsZero ((ProjectiveResolution.Vanishing.cohomology (R := R) (σ := σ) (q + 1)).obj
      (ArithmeticGeometry.OrdinaryLocus.Openness.SheafHomModule.Construction.sheafHomModule M (AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j b))) := by
  obtain ⟨r, d, hd, ⟨e⟩⟩ := h
  let F := SchemeInternalHom.functor (AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j b) ⋙
    ProjectiveResolution.Vanishing.cohomology (R := R) (σ := σ) (q + 1)
  exact (Projective.InternalHomVanishing.coproduct_isZero j d b
    (fun i => hb.trans (hd i)) q).of_iso (F.mapIso e.op).symm

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.NegativeTerms
