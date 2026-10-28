import OAI.NumberTheory.Quaternion.Arithmetic.LocalExpDerivative
import OAI.NumberTheory.ArithmeticGroups.Lattices.Infinitesimal.Action
import Mathlib.Analysis.Analytic.Order
import OAI.NumberTheory.ArithmeticGroups.Lattices.CoordinateIdeal

/-! # Local Exp Integration -/

namespace OAI.NumberTheory.Quaternion.Arithmetic.LocalExpIntegration

noncomputable section

section

/-! Polynomial functions along local exponential curves. All derivative
identities are asserted only where the exponential series converges. -/

open scoped Classical _root_.Matrix.Norms.Operator
open _root_.MvPolynomial NormedSpace Filter _root_.Topology

variable {K : Type} [NontriviallyNormedField K] [CharZero K] [CompleteSpace K] {n : ℕ}

local instance localExpPolynomialMatrixComplete :
    @CompleteSpace (Matrix (Fin n) (Fin n) K)
      (inferInstance : NormedRing (Matrix (Fin n) (Fin n) K)).toUniformSpace :=
  FiniteDimensional.complete K _

def localExponentialPolynomial (A : Matrix (Fin n) (Fin n) K)
    (p : ArithmeticGroups.Lattices.Algebraic.CoordinatePolynomial n K) : K → K :=
  fun t => eval (fun ij => exp (t • A) ij.1 ij.2) p

def localMatrixEntryCLM (i j : Fin n) : Matrix (Fin n) (Fin n) K →L[K] K :=
  (show Matrix (Fin n) (Fin n) K →ₗ[K] K from
    { toFun := fun M => M i j
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }).toContinuousLinearMap

theorem local_matrix_exp_entry_hasDerivAt
    (hr : 0 < (expSeries K (Matrix (Fin n) (Fin n) K)).radius)
    (A : Matrix (Fin n) (Fin n) K) (t : K)
    (ht : t • A ∈ Metric.eball 0 (expSeries K (Matrix (Fin n) (Fin n) K)).radius)
    (i j : Fin n) :
    HasDerivAt (fun s : K => exp (s • A) i j) ((exp (t • A) * A) i j) t := by
  convert! (localMatrixEntryCLM (K := K) i j).hasFDerivAt.comp_hasDerivAt t
    (LocalExpDerivative.local_exp_smul_hasDerivAt hr A t ht)

theorem local_matrix_exp_entry_analyticAt (A : Matrix (Fin n) (Fin n) K) (t : K)
    (ht : t • A ∈ Metric.eball 0 (expSeries K (Matrix (Fin n) (Fin n) K)).radius)
    (i j : Fin n) : AnalyticAt K (fun s : K => exp (s • A) i j) t := by
  have hs : AnalyticAt K (fun s : K => s • A) t := analyticAt_id.smul analyticAt_const
  have he : AnalyticAt K (fun s : K => exp (s • A)) t :=
    (analyticAt_exp_of_mem_ball (t • A) ht).comp (f := fun s : K => s • A) hs
  exact ((localMatrixEntryCLM i j).analyticAt _).comp (f := fun s : K => exp (s • A)) he

theorem localExponentialPolynomial_hasDerivAt
    (hr : 0 < (expSeries K (Matrix (Fin n) (Fin n) K)).radius)
    (A : Matrix (Fin n) (Fin n) K) (p : ArithmeticGroups.Lattices.Algebraic.CoordinatePolynomial n K) (t : K)
    (ht : t • A ∈ Metric.eball 0 (expSeries K (Matrix (Fin n) (Fin n) K)).radius) :
    HasDerivAt (localExponentialPolynomial A p)
      (localExponentialPolynomial A (ArithmeticGroups.Lattices.Infinitesimal.Action.Construction.rightInfinitesimal A p) t) t := by
  induction p using MvPolynomial.induction_on with
  | C c =>
    unfold localExponentialPolynomial
    simpa using hasDerivAt_const t c
  | add p q hp hq =>
    unfold localExponentialPolynomial at hp hq ⊢
    simpa only [map_add, Pi.add_def] using hp.add hq
  | mul_X p ij hp =>
    obtain ⟨i, j⟩ := ij
    have hX := local_matrix_exp_entry_hasDerivAt hr A t ht i j
    unfold localExponentialPolynomial at hp ⊢
    convert! hp.mul hX using 1
    · simp only [map_mul, eval_X]
      rfl
    · simp only [Derivation.leibniz, smul_eq_mul,
        ArithmeticGroups.Lattices.Infinitesimal.Action.Construction.rightInfinitesimal_X, map_add, map_mul, map_sum, eval_X, eval_C, Matrix.mul_apply]
      ring

theorem localExponentialPolynomial_analyticAt (A : Matrix (Fin n) (Fin n) K)
    (p : ArithmeticGroups.Lattices.Algebraic.CoordinatePolynomial n K) (t : K)
    (ht : t • A ∈ Metric.eball 0 (expSeries K (Matrix (Fin n) (Fin n) K)).radius) :
    AnalyticAt K (localExponentialPolynomial A p) t := by
  induction p using MvPolynomial.induction_on with
  | C c =>
    unfold localExponentialPolynomial
    simpa using (analyticAt_const (𝕜 := K) (v := c))
  | add p q hp hq =>
    unfold localExponentialPolynomial at hp hq ⊢
    simpa only [map_add, Pi.add_def] using hp.add hq
  | mul_X p ij hp =>
    obtain ⟨i, j⟩ := ij
    unfold localExponentialPolynomial at hp ⊢
    simpa only [map_mul, eval_X, Pi.mul_def] using
      hp.mul (local_matrix_exp_entry_analyticAt A t ht i j)

theorem localExponentialPolynomial_deriv_eventually
    (hr : 0 < (expSeries K (Matrix (Fin n) (Fin n) K)).radius)
    (A : Matrix (Fin n) (Fin n) K) (p : ArithmeticGroups.Lattices.Algebraic.CoordinatePolynomial n K) :
    deriv (localExponentialPolynomial A p) =ᶠ[𝓝 0]
      localExponentialPolynomial A (ArithmeticGroups.Lattices.Infinitesimal.Action.Construction.rightInfinitesimal A p) := by
  have hnear : ∀ᶠ t : K in 𝓝 0,
      t • A ∈ Metric.eball 0 (expSeries K (Matrix (Fin n) (Fin n) K)).radius :=
    LocalExpDerivative.local_exp_smul_eventually_mem_ball hr A
  filter_upwards [hnear] with t ht
  exact (localExponentialPolynomial_hasDerivAt hr A p t ht).deriv

theorem localExponentialPolynomial_iteratedDeriv_eventually
    (hr : 0 < (expSeries K (Matrix (Fin n) (Fin n) K)).radius)
    (A : Matrix (Fin n) (Fin n) K) (p : ArithmeticGroups.Lattices.Algebraic.CoordinatePolynomial n K) (r : ℕ) :
    iteratedDeriv r (localExponentialPolynomial A p) =ᶠ[𝓝 0]
      localExponentialPolynomial A ((ArithmeticGroups.Lattices.Infinitesimal.Action.Construction.rightInfinitesimal A)^[r] p) := by
  induction r generalizing p with
  | zero => exact Filter.EventuallyEq.rfl
  | succ r hr' =>
    rw [iteratedDeriv_succ', Function.iterate_succ_apply]
    exact ((localExponentialPolynomial_deriv_eventually hr A p).iteratedDeriv r).trans (hr' _)

end

/-! Infinitesimal ideal preservation integrates to group membership near
zero over any complete normed field with positive exponential radius. -/

open scoped Classical _root_.Matrix.Norms.Operator
open _root_.MvPolynomial NormedSpace Set Filter _root_.Topology

variable {K : Type} [NontriviallyNormedField K] [CharZero K] [CompleteSpace K] {n : ℕ}

theorem analytic_eventually_zero_of_iteratedDeriv_zero
    {f : K → K} (hf : AnalyticAt K f 0)
    (hzero : ∀ r, iteratedDeriv r f 0 = 0) : f =ᶠ[𝓝 0] 0 := by
  apply analyticOrderAt_eq_top.mp
  rw [ENat.eq_top_iff_forall_ge]
  intro r
  exact (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hf).mpr (fun i _ => hzero i)

omit [CharZero K] [CompleteSpace K] in
theorem local_iterate_infinitesimal_mem_ideal (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup K n)
    {A : Matrix (Fin n) (Fin n) K} (hA : A ∈ ArithmeticGroups.Lattices.Infinitesimal.Action.Construction.infinitesimalStabilizer G)
    {p : ArithmeticGroups.Lattices.Algebraic.CoordinatePolynomial n K} (hp : p ∈ ArithmeticGroups.Lattices.VanishingIdeal.Construction.coordinateVanishingIdeal G) (r : ℕ) :
    (ArithmeticGroups.Lattices.Infinitesimal.Action.Construction.rightInfinitesimal A)^[r] p ∈ ArithmeticGroups.Lattices.VanishingIdeal.Construction.coordinateVanishingIdeal G := by
  induction r with
  | zero => exact hp
  | succ r hr =>
    rw [Function.iterate_succ_apply']
    exact (ArithmeticGroups.Lattices.Infinitesimal.Action.Construction.mem_infinitesimalStabilizer G A).mp hA _ hr

omit [CharZero K] [CompleteSpace K] in
theorem localExponentialPolynomial_zero (A : Matrix (Fin n) (Fin n) K)
    (p : ArithmeticGroups.Lattices.Algebraic.CoordinatePolynomial n K) :
    localExponentialPolynomial A p 0 = ArithmeticGroups.Lattices.Algebraic.evaluateMatrix (RingHom.id K) (1 : ArithmeticGroups.Lattices.Algebraic.SL n K) p := by
  simp only [localExponentialPolynomial, zero_smul, exp_zero, ArithmeticGroups.Lattices.Algebraic.evaluateMatrix]
  rfl

theorem localExponentialPolynomial_eventually_zero
    (hr : 0 < (expSeries K (Matrix (Fin n) (Fin n) K)).radius)
    (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup K n) {A : Matrix (Fin n) (Fin n) K}
    (hA : A ∈ ArithmeticGroups.Lattices.Infinitesimal.Action.Construction.infinitesimalStabilizer G)
    {p : ArithmeticGroups.Lattices.Algebraic.CoordinatePolynomial n K} (hp : p ∈ ArithmeticGroups.Lattices.VanishingIdeal.Construction.coordinateVanishingIdeal G) :
    localExponentialPolynomial A p =ᶠ[𝓝 0] 0 := by
  apply analytic_eventually_zero_of_iteratedDeriv_zero
    (localExponentialPolynomial_analyticAt A p 0 (by simpa using hr))
  intro r
  rw [(localExponentialPolynomial_iteratedDeriv_eventually hr A p r).eq_of_nhds,
    localExponentialPolynomial_zero]
  exact local_iterate_infinitesimal_mem_ideal G hA hp r K (RingHom.id K) (1 : G.RationalPoints)

theorem local_infinitesimal_exp_eventually_mem
    (hr : 0 < (expSeries K (Matrix (Fin n) (Fin n) K)).radius)
    (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup K n) {A : Matrix (Fin n) (Fin n) K}
    (hA : A ∈ ArithmeticGroups.Lattices.Infinitesimal.Action.Construction.infinitesimalStabilizer G) :
    ∀ᶠ t : K in 𝓝 0,
      exp (t • A) ∈ range (fun g : G.RationalPoints => (g.val : Matrix (Fin n) (Fin n) K)) := by
  obtain ⟨S, hS⟩ := ArithmeticGroups.Lattices.VanishingIdeal.Construction.vanishingIdeal_finitely_generated G
  have hnear : ∀ᶠ t : K in 𝓝 0, ∀ p ∈ S, localExponentialPolynomial A p t = 0 := by
    apply S.eventually_all.mpr
    intro p hp
    apply localExponentialPolynomial_eventually_zero hr G hA
    rw [← hS]
    exact Ideal.subset_span hp
  filter_upwards [hnear] with t ht
  let e : ArithmeticGroups.Lattices.Algebraic.CoordinatePolynomial n K →+* K := eval (fun ij => exp (t • A) ij.1 ij.2)
  have hker : ArithmeticGroups.Lattices.VanishingIdeal.Construction.coordinateVanishingIdeal G ≤ RingHom.ker e := by
    rw [← hS]
    exact Ideal.span_le.mpr ht
  have hdet : (exp (t • A)).det = 1 := by
    have hz := hker (ArithmeticGroups.Lattices.CoordinateIdeal.Construction.definingIdeal_le_vanishingIdeal G
      (Ideal.subset_span (mem_insert (ArithmeticGroups.Lattices.CoordinateIdeal.Construction.determinantEquation K n) G.equations)))
    change eval₂Hom (RingHom.id K) (fun ij => exp (t • A) ij.1 ij.2)
      (ArithmeticGroups.Lattices.CoordinateIdeal.Construction.determinantEquation K n) = 0 at hz
    rw [ArithmeticGroups.Lattices.CoordinateIdeal.Construction.eval_determinantEquation] at hz
    exact sub_eq_zero.mp hz
  let g : ArithmeticGroups.Lattices.Algebraic.SL n K := ⟨exp (t • A), hdet⟩
  have hg : g ∈ G.subgroup K (RingHom.id K) := by
    apply (G.mem_iff K (RingHom.id K) g).mpr
    intro p hp
    exact hker (ArithmeticGroups.Lattices.VanishingIdeal.Construction.equations_subset_vanishingIdeal G hp)
  exact ⟨⟨g, hg⟩, rfl⟩

end

end OAI.NumberTheory.Quaternion.Arithmetic.LocalExpIntegration
