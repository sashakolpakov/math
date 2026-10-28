import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.CrystallineGroupLaw
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.CrystallineEndAction
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.Specialization

/-! # Crystalline -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Crystalline.CM.Hecke

noncomputable section

/-! GeometricComparison's actual Hecke presentations agree with the rational action
on crystalline H1. The same comparison carries their Frobenius polynomial
to the specified de Rham operators. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped TensorProduct
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.CrystallineEndAction.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Specialized.CM.Hecke

variable {K : Type} [Field K] [NumberField K]
  {q : ℕ} [Fact q.Prime] {jq : K →+* ℚ_[q]} (A : NumberTheory.PadicHodge.GeometricComparison.Geometry.AbelianH1Model K q jq)
  {H : Type} [CommRing H] [Algebra ℚ H] (ρ : A.HeckeRealization H)

def crystallineHecke (h : H) : Module.End ℚ_[q] A.Crystalline :=
  (ρ.presentation h).sum (fun f r => (r : ℚ_[q]) • A.crystallinePullback f)

theorem crystallineFrobenius_eq_pullback : A.crystallineFrobenius =
    NumberTheory.PadicHodge.GeometricComparison.Crystalline.CoefficientAdapter.rationalPullback q (FormalGeometry.Completion.Frobenius.Construction.finiteFieldSchemeFrobenius (ZMod q) A.specialFiber.scheme) := rfl

theorem rationalAction_specializedHecke
    (hgroup : CrystallineMonoidAction.CM.End.GroupLawIdentity q A.specialFiber.scheme) (h : H) :
    CrystallineEndAction.CM.rationalAction q A.specialFiber.scheme hgroup
      (MulOpposite.op (Specialized.CM.Hecke.specializedHeckeAction A ρ h)) = crystallineHecke A ρ h := by
  let act : FormalGeometry.Completion.Endomorphisms.Construction.RationalAlgebraicEnd A.specialFiber.scheme →+ Module.End ℚ_[q] A.Crystalline :=
    (CrystallineEndAction.CM.rationalAction q A.specialFiber.scheme hgroup).toRingHom.toAddMonoidHom.comp
      MulOpposite.opAddEquiv.toAddMonoidHom
  change act (Specialized.CM.Hecke.specializedHeckeAction A ρ h) = _
  rw [← Specialized.CM.Hecke.specializedHeckeAction_presentation, map_finsuppSum]
  apply Finsupp.sum_congr
  intro f _
  change CrystallineEndAction.CM.rationalAction q A.specialFiber.scheme hgroup
    (MulOpposite.op ((ρ.presentation h f) ⊗ₜ[ℤ] Specialized.CM.Hecke.specialEndOfExtending A f)) = _
  rw [CrystallineEndAction.CM.rationalAction_tmul]
  rfl

theorem comparison_hecke
    (cmp : A.Crystalline ≃ₗ[ℚ_[q]] A.DeRham)
    (hc : ∀ f x, cmp (A.crystallinePullback f x) = A.deRhamPullback f (cmp x))
    (h : H) (x : A.Crystalline) :
    cmp (crystallineHecke A ρ h x) = A.deRhamHecke ρ h (cmp x) := by
  simp only [crystallineHecke, NumberTheory.PadicHodge.GeometricComparison.Geometry.AbelianH1Model.deRhamHecke, Finsupp.sum,
    LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, hc]

theorem comparison_conj_hecke
    (cmp : A.Crystalline ≃ₗ[ℚ_[q]] A.DeRham)
    (hc : ∀ f x, cmp (A.crystallinePullback f x) = A.deRhamPullback f (cmp x)) (h : H) :
    cmp.conjRingEquiv (crystallineHecke A ρ h) = A.deRhamHecke ρ h := by
  apply LinearMap.ext
  intro x
  change cmp (crystallineHecke A ρ h (cmp.symm x)) = _
  rw [comparison_hecke A ρ cmp hc, cmp.apply_symm_apply]

theorem crystallineHecke_commute
    (hgroup : CrystallineMonoidAction.CM.End.GroupLawIdentity q A.specialFiber.scheme) (h k : H) :
    Commute (crystallineHecke A ρ h) (crystallineHecke A ρ k) := by
  have hs : Commute (Specialized.CM.Hecke.specializedHeckeAction A ρ h) (Specialized.CM.Hecke.specializedHeckeAction A ρ k) := by
    change Specialized.CM.Hecke.specializedHeckeAction A ρ h * Specialized.CM.Hecke.specializedHeckeAction A ρ k = _
    rw [← map_mul, mul_comm h k, map_mul]
  have hm := hs.op.map (CrystallineEndAction.CM.rationalAction q A.specialFiber.scheme hgroup)
  simpa only [rationalAction_specializedHecke] using hm

theorem crystallineFrobenius_hecke_commute
    (hgroup : CrystallineMonoidAction.CM.End.GroupLawIdentity q A.specialFiber.scheme) (h : H) :
    Commute A.crystallineFrobenius (crystallineHecke A ρ h) := by
  have hm := (FormalGeometry.Completion.Endomorphisms.Construction.rationalAlgebraicFrobenius_commutes (ZMod q) A.specialFiber.scheme
    (Specialized.CM.Hecke.specializedHeckeAction A ρ h)).op.map (CrystallineEndAction.CM.rationalAction q A.specialFiber.scheme hgroup)
  rw [crystallineFrobenius_eq_pullback]
  simpa only [CrystallineEndAction.CM.rationalAction_frobenius, rationalAction_specializedHecke] using hm

theorem deRhamHecke_commute
    (hgroup : CrystallineMonoidAction.CM.End.GroupLawIdentity q A.specialFiber.scheme)
    (cmp : A.Crystalline ≃ₗ[ℚ_[q]] A.DeRham)
    (hc : ∀ f x, cmp (A.crystallinePullback f x) = A.deRhamPullback f (cmp x)) (h k : H) :
    Commute (A.deRhamHecke ρ h) (A.deRhamHecke ρ k) := by
  have hm := (crystallineHecke_commute A ρ hgroup h k).map cmp.conjRingEquiv
  simpa only [comparison_conj_hecke A ρ cmp hc] using hm

theorem deRhamFrobenius_hecke_commute
    (hgroup : CrystallineMonoidAction.CM.End.GroupLawIdentity q A.specialFiber.scheme)
    (cmp : A.Crystalline ≃ₗ[ℚ_[q]] A.DeRham)
    (hc : ∀ f x, cmp (A.crystallinePullback f x) = A.deRhamPullback f (cmp x)) (h : H) :
    Commute (cmp.conjRingEquiv A.crystallineFrobenius) (A.deRhamHecke ρ h) := by
  have hm := (crystallineFrobenius_hecke_commute A ρ hgroup h).map cmp.conjRingEquiv
  simpa only [comparison_conj_hecke A ρ cmp hc] using hm

theorem comparisonFrobenius_linear
    (cmp : A.Crystalline ≃ₗ[ℚ_[q]] A.DeRham)
    (phi : A.Crystalline ≃ₗ[ℚ_[q]] A.Crystalline)
    (hphi : phi.toLinearMap = A.crystallineFrobenius) :
    cmp.conjRingEquiv A.crystallineFrobenius =
      (cmp.symm.trans (phi.trans cmp)).toLinearMap := by
  rw [← hphi]
  rfl

theorem crystalline_polynomial_from_specialized
    (hgroup : CrystallineMonoidAction.CM.End.GroupLawIdentity q A.specialFiber.scheme) (h : Fin 3 → H)
    (hp : Ordinary.Polynomial.CM.heckePolynomialValue q
      (FormalGeometry.Completion.Endomorphisms.Construction.rationalAlgebraicFrobenius (ZMod q) A.specialFiber.scheme)
      (fun i => Specialized.CM.Hecke.specializedHeckeAction A ρ (h i)) = 0) :
    Ordinary.Polynomial.CM.heckePolynomialValue q A.crystallineFrobenius
      (fun i => crystallineHecke A ρ (h i)) = 0 := by
  have hc := CrystallineEndAction.CM.crystalline_polynomial q A.specialFiber.scheme hgroup
    (fun i => Specialized.CM.Hecke.specializedHeckeAction A ρ (h i)) hp
  rw [crystallineFrobenius_eq_pullback]
  simpa only [rationalAction_specializedHecke] using hc

theorem deRham_polynomial_from_crystalline
    (cmp : A.Crystalline ≃ₗ[ℚ_[q]] A.DeRham)
    (hc : ∀ f x, cmp (A.crystallinePullback f x) = A.deRhamPullback f (cmp x))
    (h : Fin 3 → H)
    (hp : Ordinary.Polynomial.CM.heckePolynomialValue q A.crystallineFrobenius
      (fun i => crystallineHecke A ρ (h i)) = 0) :
    Ordinary.Polynomial.CM.heckePolynomialValue q (cmp.conjRingEquiv A.crystallineFrobenius)
      (fun i => A.deRhamHecke ρ (h i)) = 0 := by
  have hmap := congrArg cmp.conjRingEquiv hp
  simpa only [Ordinary.Polynomial.CM.heckePolynomialValue, map_sub, map_add,
    map_mul, map_pow, map_nsmul, map_zero, comparison_conj_hecke A ρ cmp hc] using hmap

/-- The full comparison prerequisite supplies the H1 group law on the
product model. The original model's comparison then transports the
actual special-fiber polynomial with its given Hecke presentations. -/
theorem deRham_polynomial_from_full_GeometricComparison
    (hGeometricComparison : NumberTheory.PadicHodge.GeometricComparisonAdapter.CM.ExtremeSlopes.GeometricComparisonInput)
    (κ : K →+* AlgebraicClosure ℚ) (jComplex : AlgebraicClosure ℚ →+* ℂ)
    (iota : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ_[q])
    (hplace : (algebraMap ℚ_[q] (AlgebraicClosure ℚ_[q])).comp jq = iota.comp κ)
    (P : Foundations.Scheme.SmoothProjective.ProjectivePresentation (A.complexFiber (jComplex.comp κ)).scheme.left
      (A.complexFiber (jComplex.comp κ)).scheme.hom)
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓq : ℓ ≠ q)
    (cmp : A.Crystalline ≃ₗ[ℚ_[q]] A.DeRham)
    (hc : ∀ f x, cmp (A.crystallinePullback f x) = A.deRhamPullback f (cmp x))
    (h : Fin 3 → H)
    (hp : Ordinary.Polynomial.CM.heckePolynomialValue q
      (FormalGeometry.Completion.Endomorphisms.Construction.rationalAlgebraicFrobenius (ZMod q) A.specialFiber.scheme)
      (fun i => Specialized.CM.Hecke.specializedHeckeAction A ρ (h i)) = 0) :
    Ordinary.Polynomial.CM.heckePolynomialValue q (cmp.conjRingEquiv A.crystallineFrobenius)
      (fun i => A.deRhamHecke ρ (h i)) = 0 :=
  deRham_polynomial_from_crystalline A ρ cmp hc h
    (crystalline_polynomial_from_specialized A ρ
      (CrystallineGroupLaw.CM.groupLaw_from_full_GeometricComparison A hGeometricComparison κ jComplex iota hplace P ℓ hℓq) h hp)

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Crystalline.CM.Hecke
