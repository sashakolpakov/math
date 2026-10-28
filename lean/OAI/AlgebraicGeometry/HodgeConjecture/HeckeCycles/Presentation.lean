import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ExtendingEndomorphisms
import OAI.NumberTheory.PadicHodge.GeometricComparison.HeckeScalar

/-! # Presentation -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Presentation.CM.Hecke

noncomputable section

/-! Construct GeometricComparison's Hecke realization from TateComparison's actual rational
endomorphisms and denominator clearings. Every representative extends
over the integral model by the proved Néron extension theorem. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj TensorProduct
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.EndomorphismComparison.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ExtendingEndomorphisms.CM

theorem clearing_presentation {S : Scheme} (A : Over S) [GrpObj A] [IsCommMonObj A]
    (n : ℕ) (hn : 0 < n) (a : AbelianScheme.TateComparison.End.IntegralEnd A) (f : AbelianScheme.TateComparison.End.RationalEnd A)
    (h : n • f = AbelianScheme.TateComparison.End.endToRational A a) :
    ((n : ℚ)⁻¹) ⊗ₜ[ℤ] EndomorphismComparison.CM.integralEquiv A a = EndomorphismComparison.CM.rationalEquiv A f := by
  have hnQ : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  calc
    _ = (n : ℚ)⁻¹ • ((1 : ℚ) ⊗ₜ[ℤ] EndomorphismComparison.CM.integralEquiv A a) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    _ = (n : ℚ)⁻¹ • (n • EndomorphismComparison.CM.rationalEquiv A f) :=
      congrArg (fun x => (n : ℚ)⁻¹ • x) (EndomorphismComparison.CM.transports_clearing A n a f h).symm
    _ = EndomorphismComparison.CM.rationalEquiv A f := by
      rw [← Nat.cast_smul_eq_nsmul ℚ, smul_smul, inv_mul_cancel₀ hnQ, one_smul]

variable {K : Type} [Field K] [NumberField K]
  {q : ℕ} [Fact q.Prime] {jq : K →+* ℚ_[q]}
  (A : NumberTheory.PadicHodge.GeometricComparison.Geometry.AbelianH1Model K q jq)

def extendingEndomorphism (f : FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd A.variety.scheme) : A.ExtendingEndomorphism := by
  let e : (A.integral.pullback
      (Spec.map (CommRingCat.ofHom (algebraMap ℤ_[q] ℚ_[q])))).scheme ≅
      (A.variety.pullback (Spec.map (CommRingCat.ofHom jq))).scheme := A.genericIso
  let : IsMonHom e.hom := A.genericIso_group
  have h := ExtendingEndomorphisms.CM.exists_compatible_integral_endomorphism A.variety A.integral jq e f
  exact { generic := f, integral := h.choose, compatible := h.choose_spec }

theorem extendingEndomorphism_generic (f : FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd A.variety.scheme) :
    (extendingEndomorphism A f).generic = f := rfl

/-- GeometricComparison's input is a proved presentation of the same endomorphism-algebra
action. No comparison, weak admissibility, or slope conclusion is assumed. -/
theorem exists_hecke_realization
    {H : Type} [CommRing H] [Algebra ℚ H]
    (ρ : H →ₐ[ℚ] AbelianScheme.TateComparison.End.RationalEnd A.variety.scheme)
    (hclear : ∀ h : H, ∃ n : ℕ, 0 < n ∧ ∃ a : AbelianScheme.TateComparison.End.IntegralEnd A.variety.scheme,
      n • ρ h = AbelianScheme.TateComparison.End.endToRational A.variety.scheme a) :
    ∃ R : A.HeckeRealization H,
      R.action = (EndomorphismComparison.CM.rationalEquiv A.variety.scheme).toAlgHom.comp ρ := by
  classical
  choose n hn a ha using hclear
  refine ⟨{
    action := (EndomorphismComparison.CM.rationalEquiv A.variety.scheme).toAlgHom.comp ρ
    presentation := fun h => Finsupp.single
      (extendingEndomorphism A (EndomorphismComparison.CM.integralEquiv A.variety.scheme (a h))) ((n h : ℚ)⁻¹)
    represents := ?_ }, rfl⟩
  intro h
  simp only [Finsupp.sum_single_index, TensorProduct.zero_tmul, extendingEndomorphism_generic]
  exact clearing_presentation A.variety.scheme (n h) (hn h) (a h) (ρ h) (ha h)

/-- TateComparison's denominator equation identifies the resulting GeometricComparison Betti
operators with the original rational action, for the same chosen clearings. -/
theorem exists_hecke_realization_with_betti
    {H : Type} [CommRing H] [Algebra ℚ H]
    (ρ : H →ₐ[ℚ] AbelianScheme.TateComparison.End.RationalEnd A.variety.scheme)
    (hclear : ∀ h : H, ∃ n : ℕ, 0 < n ∧ ∃ a : AbelianScheme.TateComparison.End.IntegralEnd A.variety.scheme,
      n • ρ h = AbelianScheme.TateComparison.End.endToRational A.variety.scheme a)
    (j : K →+* ℂ) (T : H → Module.End ℚ (A.Betti j))
    (hbetti : ∀ h (n : ℕ), 0 < n → ∀ a : AbelianScheme.TateComparison.End.IntegralEnd A.variety.scheme,
      n • ρ h = AbelianScheme.TateComparison.End.endToRational A.variety.scheme a →
        (n : ℚ) • T h = A.bettiPullback j
          (extendingEndomorphism A (EndomorphismComparison.CM.integralEquiv A.variety.scheme a))) :
    ∃ R : A.HeckeRealization H,
      R.action = (EndomorphismComparison.CM.rationalEquiv A.variety.scheme).toAlgHom.comp ρ ∧
      A.bettiHecke j R = T := by
  classical
  choose n hn a ha using hclear
  let R : A.HeckeRealization H := {
    action := (EndomorphismComparison.CM.rationalEquiv A.variety.scheme).toAlgHom.comp ρ
    presentation := fun h => Finsupp.single
      (extendingEndomorphism A (EndomorphismComparison.CM.integralEquiv A.variety.scheme (a h))) ((n h : ℚ)⁻¹)
    represents := fun h => by
      simp only [Finsupp.sum_single_index, TensorProduct.zero_tmul,
        extendingEndomorphism_generic]
      exact clearing_presentation A.variety.scheme (n h) (hn h) (a h) (ρ h) (ha h) }
  refine ⟨R, rfl, ?_⟩
  funext h
  change (Finsupp.single _ ((n h : ℚ)⁻¹)).sum
    (fun f b => b • A.bettiPullback j f) = T h
  rw [Finsupp.sum_single_index (by simp), ← hbetti h (n h) (hn h) (a h) (ha h)]
  rw [smul_smul, inv_mul_cancel₀ (Nat.cast_ne_zero.mpr (hn h).ne'), one_smul]

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Presentation.CM.Hecke
