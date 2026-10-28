import Mathlib.Algebra.Polynomial.Module.TensorProduct
import Mathlib.Algebra.Category.ModuleCat.ProjectiveDimension

/-! # Resolution -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Polynomial.Resolution

noncomputable section

/-! The polynomial-module resolution sequence. For an R[X]-module M,
the induced module M[X] maps onto M by evaluation at the action of X;
the kernel is the image of X minus that coefficientwise action. -/

open _root_.Polynomial

universe u

variable (R M : Type u) [CommRing R] [AddCommGroup M] [Module R M]
  [Module R[X] M] [IsScalarTower R R[X] M]

def variableAction : M →ₗ[R] M where
  toFun m := (X : R[X]) • m
  map_add' _ _ := smul_add _ _ _
  map_smul' _ _ := smul_comm _ _ _

def coefficientAction : PolynomialModule R M →ₗ[R[X]] PolynomialModule R M where
  toFun := PolynomialModule.map R (variableAction R M)
  map_add' := map_add _
  map_smul' p m := by
    simpa using
      (PolynomialModule.map_smul R (variableAction R M) p m)

def delta : PolynomialModule R M →ₗ[R[X]] PolynomialModule R M :=
  (X : R[X]) • LinearMap.id - coefficientAction R M

def evaluationLinear : PolynomialModule R M →ₗ[R] M :=
  ((PolynomialModule.eval (R := R[X]) (M := M) X).restrictScalars R).comp
    (PolynomialModule.map R[X] (LinearMap.id : M →ₗ[R] M))

theorem evaluation_single (n : ℕ) (m : M) :
    evaluationLinear R M (PolynomialModule.single R n m) = (X : R[X]) ^ n • m := by
  simp [evaluationLinear]

theorem evaluation_smul (p : R[X]) (f : PolynomialModule R M) :
    evaluationLinear R M (p • f) = p • evaluationLinear R M f := by
  induction f using PolynomialModule.induction_linear with
  | zero => simp
  | add f g hf hg => simp only [smul_add, map_add, hf, hg]
  | single n m =>
    induction p using Polynomial.induction_on' with
    | add p q hp hq => simp only [add_smul, map_add, hp, hq]
    | monomial i r =>
      rw [PolynomialModule.monomial_smul_single, evaluation_single, evaluation_single,
        ← Polynomial.C_mul_X_pow_eq_monomial]
      calc
        _ = r • ((X : R[X]) ^ (i + n) • m) := smul_comm _ _ _
        _ = C r • ((X : R[X]) ^ (i + n) • m) :=
          (IsScalarTower.algebraMap_smul (R := R) R[X] r _).symm
        _ = _ := by rw [mul_smul, ← mul_smul (X ^ i) (X ^ n), ← pow_add]

def evaluation : PolynomialModule R M →ₗ[R[X]] M where
  toFun := evaluationLinear R M
  map_add' := map_add _
  map_smul' := evaluation_smul R M

theorem delta_single (n : ℕ) (m : M) :
    delta R M (PolynomialModule.single R n m) = PolynomialModule.single R (n + 1) m -
      PolynomialModule.single R n ((X : R[X]) • m) := by
  simp only [delta, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
    coefficientAction, LinearMap.coe_mk, AddHom.coe_mk, PolynomialModule.map_single,
    variableAction, ← monomial_one_one_eq_X, PolynomialModule.monomial_smul_single,
    one_smul, add_comm 1 n]

theorem evaluation_delta (f : PolynomialModule R M) :
    evaluation R M (delta R M f) = 0 := by
  induction f using PolynomialModule.induction_linear with
  | zero => simp
  | add f g hf hg => simp only [map_add, hf, hg, add_zero]
  | single n m =>
    rw [delta_single, map_sub]
    change evaluationLinear R M _ - evaluationLinear R M _ = 0
    rw [evaluation_single, evaluation_single, smul_smul, pow_succ, sub_self]

theorem evaluation_surjective : Function.Surjective (evaluation R M) := by
  intro m
  refine ⟨PolynomialModule.single R 0 m, ?_⟩
  change evaluationLinear R M _ = _
  simp [evaluation_single]

theorem delta_coeff_succ (f : PolynomialModule R M) (n : ℕ) :
    (delta R M f).coeff (n + 1) = f.coeff n - (X : R[X]) • f.coeff (n + 1) := by
  change (((X : R[X]) • f).coeff - (PolynomialModule.map R (variableAction R M) f).coeff) (n + 1) = _
  rw [Finsupp.sub_apply, ← monomial_one_one_eq_X, PolynomialModule.monomial_smul_apply]
  simp only [Nat.le_add_left, ite_true, Nat.add_sub_cancel_right, one_smul]
  rfl

theorem delta_injective : Function.Injective (delta R M) := by
  rw [injective_iff_map_eq_zero]
  intro f hf
  by_contra hn
  have hs : f.coeff.support.Nonempty := Finsupp.support_nonempty_iff.mpr
    (fun h => hn (PolynomialModule.coeff_injective h))
  let n := f.coeff.support.max' hs
  have hmem : n ∈ f.coeff.support := Finset.max'_mem _ _
  have hnext : f.coeff (n + 1) = 0 := by
    apply Finsupp.notMem_support_iff.mp
    intro h
    have := Finset.le_max' f.coeff.support (n + 1) h
    omega
  have h := congrArg (fun p : PolynomialModule R M => p.coeff (n + 1)) hf
  rw [delta_coeff_succ, hnext, smul_zero, sub_zero] at h
  exact Finsupp.mem_support_iff.mp hmem h

def monomialPreimage : ℕ → M → PolynomialModule R M
  | 0, _ => 0
  | n + 1, m => PolynomialModule.single R n m + monomialPreimage n ((X : R[X]) • m)

theorem delta_monomialPreimage (n : ℕ) (m : M) :
    delta R M (Resolution.monomialPreimage R M n m) = PolynomialModule.single R n m -
      PolynomialModule.single R 0 ((X : R[X]) ^ n • m) := by
  induction n generalizing m with
  | zero => simp [Resolution.monomialPreimage]
  | succ n ih =>
    rw [Resolution.monomialPreimage, map_add, delta_single, ih, smul_smul, ← pow_succ]
    abel

theorem exists_delta_preimage (f : PolynomialModule R M) :
    ∃ g, delta R M g = f - PolynomialModule.single R 0 (evaluation R M f) := by
  induction f using PolynomialModule.induction_linear with
  | zero => exact ⟨0, by simp⟩
  | add f g hf hg =>
    obtain ⟨f', hf'⟩ := hf
    obtain ⟨g', hg'⟩ := hg
    refine ⟨f' + g', ?_⟩
    rw [map_add, hf', hg', map_add, PolynomialModule.single_add]
    abel
  | single n m =>
    refine ⟨Resolution.monomialPreimage R M n m, ?_⟩
    change delta R M _ = _ - PolynomialModule.single R 0 (evaluationLinear R M _)
    rw [evaluation_single]
    exact delta_monomialPreimage R M n m

theorem exact_delta_evaluation : Function.Exact (delta R M) (evaluation R M) := by
  intro f
  constructor
  · intro hf
    obtain ⟨g, hg⟩ := exists_delta_preimage R M f
    exact ⟨g, by simpa [hf] using hg⟩
  · rintro ⟨g, rfl⟩
    exact evaluation_delta R M g

def shortComplex : CategoryTheory.ShortComplex (ModuleCat.{u} R[X]) :=
  ModuleCat.shortComplexOfCompEqZero (delta R M) (evaluation R M)
    (LinearMap.ext (evaluation_delta R M))

theorem shortExact : (shortComplex R M).ShortExact :=
  ModuleCat.shortComplex_shortExact _ (exact_delta_evaluation R M) (delta_injective R M)
    (evaluation_surjective R M)

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Polynomial.Resolution
