import OAI.NumberTheory.PadicHodge.GeometricComparison.HeckeScalar
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.HeckeCharacters
import OAI.AlgebraicGeometry.ComplexMultiplication.CohomologyBaseChange

/-! # Betti Comparison -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.HodgeConjecture.HeckeCycles.BettiComparison.CM

/-! The canonical coefficient-extension map identifies the rational
complexification used by CMExtraction with GeometricComparison's ordinary complex Betti space.
It intertwines the actual geometric Hecke presentations. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped TensorProduct
open OAI.NumberTheory.PadicHodge.GeometricComparison.HeckeScalar

variable {K : Type} [Field K] [NumberField K]
  {q : ℕ} [Fact q.Prime] {jq : K →+* ℚ_[q]}
  (A : NumberTheory.PadicHodge.GeometricComparison.Geometry.AbelianH1Model K q jq) (j : K →+* ℂ)

def coefficientMap : ComplexMultiplication.WeightOne.CM.Complexification (A.Betti j) →ₗ[ℂ] A.ComplexBetti j :=
  ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexification (AlgebraicGeometry.Betti.Scheme.schemePointSpace (A.complexFiber j).scheme) 1

theorem coefficientMap_tmul (a : ℂ) (x : A.Betti j) :
    coefficientMap A j (a ⊗ₜ[ℚ] x) =
      a • AlgebraicGeometry.Betti.Scheme.schemeBettiRationalInclusion (A.complexFiber j).scheme 1 x := rfl

theorem coefficientMap_pullback (f : A.ExtendingEndomorphism)
    (x : ComplexMultiplication.WeightOne.CM.Complexification (A.Betti j)) :
    coefficientMap A j ((A.bettiPullback j f).baseChange ℂ x) =
      A.complexBettiPullback j f (coefficientMap A j x) := by
  induction x using TensorProduct.inductionOn with
  | tmul a x =>
    let cx : A.ComplexBetti j := AlgebraicGeometry.Betti.Scheme.schemeBettiRationalInclusion (A.complexFiber j).scheme 1 x
    let cy : A.ComplexBetti j := AlgebraicGeometry.Betti.Scheme.schemeBettiRationalInclusion (A.complexFiber j).scheme 1
      (A.bettiPullback j f x)
    have hn : cy = A.complexBettiPullback j f cx :=
      ConcreteCategory.congr_hom
        (AlgebraicGeometry.Betti.Scheme.schemeBettiRationalInclusion_naturality (A.complexEndomorphism j f) 1) x
    exact (congrArg (fun y : A.ComplexBetti j => a • y) hn).trans
      (map_smul (A.complexBettiPullback j f) a cx).symm
  | add x y hx hy => simp only [map_add, hx, hy]

theorem coefficientMap_hecke
    {H : Type} [CommRing H] [Algebra ℚ H] (R : A.HeckeRealization H)
    (h : H) (x : ComplexMultiplication.WeightOne.CM.Complexification (A.Betti j)) :
    coefficientMap A j ((A.bettiHecke j R h).baseChange ℂ x) =
      A.complexBettiHecke j R h (coefficientMap A j x) := by
  change coefficientMap A j
    ((Module.End.baseChangeHom ℚ ℂ (A.Betti j))
      ((R.presentation h).sum (fun f a => a • A.bettiPullback j f)) x) = _
  simp only [Finsupp.sum, map_sum, LinearMap.sum_apply,
    NumberTheory.PadicHodge.GeometricComparison.Geometry.AbelianH1Model.complexBettiHecke]
  apply Finset.sum_congr rfl
  intro f _
  rw [map_smul, LinearMap.smul_apply]
  change coefficientMap A j ((R.presentation h f : ℂ) •
      (A.bettiPullback j f).baseChange ℂ x) =
    (R.presentation h f : ℂ) • A.complexBettiPullback j f (coefficientMap A j x)
  rw [map_smul, coefficientMap_pullback]

def coefficientEquiv [FiniteDimensional ℚ (A.Betti j)] :
    ComplexMultiplication.WeightOne.CM.Complexification (A.Betti j) ≃ₗ[ℂ] A.ComplexBetti j :=
  ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexificationEquiv (AlgebraicGeometry.Betti.Scheme.schemePointSpace (A.complexFiber j).scheme) 1

theorem coefficientEquiv_apply [FiniteDimensional ℚ (A.Betti j)]
    (x : ComplexMultiplication.WeightOne.CM.Complexification (A.Betti j)) : coefficientEquiv A j x = coefficientMap A j x := rfl

end AlgebraicGeometry.HodgeConjecture.HeckeCycles.BettiComparison.CM

namespace AlgebraicGeometry.HodgeConjecture.HeckeCycles.BettiComparison.CM.Summands

/-! The coefficient comparison carries CMExtraction's actual generalized Hecke
spaces onto GeometricComparison's ordinary complex Betti summands. -/

open scoped TensorProduct
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.HeckeCharacters.CM.Projectors OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.BettiComparison.CM

section Transport

variable {L U V I : Type*} [Field L] [AddCommGroup U] [Module L U]
  [AddCommGroup V] [Module L V]

theorem shift_pow_intertwines (e : U ≃ₗ[L] V) (f : Module.End L U) (g : Module.End L V)
    (h : ∀ x, e (f x) = g (e x)) (μ : L) (n : ℕ) (x : U) :
    e (((f - μ • 1) ^ n) x) = ((g - μ • 1) ^ n) (e x) := by
  induction n with
  | zero => simp only [pow_zero, Module.End.one_apply]
  | succ n hn =>
    simp only [pow_succ', Module.End.mul_apply, LinearMap.sub_apply,
      LinearMap.smul_apply, Module.End.one_apply, map_sub, map_smul, h, hn]

theorem jointSpace_mem_equiv (e : U ≃ₗ[L] V)
    (T : I → Module.End L U) (S : I → Module.End L V)
    (he : ∀ i x, e (T i x) = S i (e x)) (χ : I → L) (x : U) :
    x ∈ HeckeCharacters.CM.Projectors.jointSpace T χ ↔ e x ∈ HeckeCharacters.CM.Projectors.jointSpace S χ := by
  simp only [HeckeCharacters.CM.Projectors.jointSpace, Submodule.mem_iInf]
  apply forall_congr'
  intro i
  simp only [Module.End.mem_genEigenspace_top, LinearMap.mem_ker]
  apply exists_congr
  intro n
  rw [← shift_pow_intertwines e (T i) (S i) (he i) (χ i) n x]
  exact e.map_eq_zero_iff.symm

theorem jointSpace_map_equiv (e : U ≃ₗ[L] V)
    (T : I → Module.End L U) (S : I → Module.End L V)
    (he : ∀ i x, e (T i x) = S i (e x)) (χ : I → L) :
    (HeckeCharacters.CM.Projectors.jointSpace T χ).map e.toLinearMap = HeckeCharacters.CM.Projectors.jointSpace S χ := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact (jointSpace_mem_equiv e T S he χ x).mp hx
  · intro y hy
    refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
    exact (jointSpace_mem_equiv e T S he χ (e.symm y)).mpr
      (by simpa only [e.apply_symm_apply] using hy)

end Transport

variable {K : Type} [Field K] [NumberField K]
  {q : ℕ} [Fact q.Prime] {jq : K →+* ℚ_[q]}
  (A : NumberTheory.PadicHodge.GeometricComparison.Geometry.AbelianH1Model K q jq) (j : K →+* ℂ)
  [FiniteDimensional ℚ (A.Betti j)]

theorem betti_summand_identification
    {H : Type} [CommRing H] [Algebra ℚ H] (R : A.HeckeRealization H) (χ : H → ℂ) :
    (HeckeCharacters.CM.Projectors.jointSpace (fun h => (A.bettiHecke j R h).baseChange ℂ) χ).map
        (coefficientEquiv A j).toLinearMap = A.bettiHeckeSummand j R χ := by
  exact jointSpace_map_equiv (coefficientEquiv A j)
    (fun h => (A.bettiHecke j R h).baseChange ℂ) (A.complexBettiHecke j R)
    (fun h x => coefficientMap_hecke A j R h x) χ

end AlgebraicGeometry.HodgeConjecture.HeckeCycles.BettiComparison.CM.Summands

end

end OAI
