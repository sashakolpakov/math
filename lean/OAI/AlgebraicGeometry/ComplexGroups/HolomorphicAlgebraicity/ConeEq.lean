import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Analytic.Linear
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Multilinear.Basis
import Mathlib.LinearAlgebra.Pi
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.PrincipalIdealDomain

/-! # Cone Eq -/

namespace OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ConeEq.Constructions.Cone

noncomputable section

/-!
# Homogeneous equations for analytic cones, for HolomorphicAlgebraicity

This file develops the coefficient step of the cone proof of Chow's theorem.
Its hypotheses concern a cone and analytic equations near its vertex; they
are intermediate geometric hypotheses, not assumptions of HolomorphicAlgebraicity's conclusion.
-/

open Filter Set
open scoped _root_.Topology BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Every homogeneous Taylor term of an analytic equation vanishing on a
complex cone also vanishes on the whole cone. -/
theorem coefficient_vanishes
    {S : Set E} (hcone : ∀ (c : ℂ) ⦃x : E⦄, x ∈ S → c • x ∈ S)
    {f : E → ℂ} {p : FormalMultilinearSeries ℂ E ℂ}
    (hp : HasFPowerSeriesAt f p 0)
    (hzero : ∀ᶠ x in 𝓝 (0 : E), x ∈ S → f x = 0)
    {z : E} (hz : z ∈ S) (n : ℕ) : p n (fun _ => z) = 0 := by
  let L : ℂ →L[ℂ] E := (ContinuousLinearMap.id ℂ ℂ).smulRight z
  have hL : Tendsto L (𝓝 0) (𝓝 (0 : E)) := by
    simpa using L.continuous.continuousAt.tendsto (x := 0)
  have heq : (f ∘ L) =ᶠ[𝓝 0] 0 := by
    filter_upwards [hL.eventually hzero] with c hc
    exact hc (hcone c hz)
  have hpL : HasFPowerSeriesAt (f ∘ L) (p.compContinuousLinearMap L) 0 := by
    apply HasFPowerSeriesAt.compContinuousLinearMap
    simpa using hp
  have hcoeff := (hpL.congr heq).apply_eq_zero n 1
  change p n (fun _ => (1 : ℂ) • z) = 0 at hcoeff
  simpa only [one_smul] using hcoeff

/-- If all homogeneous coefficients vanish in a direction, the analytic
equation vanishes on a neighborhood of the vertex in that complex line. -/
theorem eventually_smul_eq_zero
    {f : E → ℂ} {p : FormalMultilinearSeries ℂ E ℂ}
    (hp : HasFPowerSeriesAt f p 0) {z : E}
    (hz : ∀ n, p n (fun _ => z) = 0) :
    ∀ᶠ c : ℂ in 𝓝 0, f (c • z) = 0 := by
  let L : ℂ →L[ℂ] E := (ContinuousLinearMap.id ℂ ℂ).smulRight z
  have hpL : HasFPowerSeriesAt (f ∘ L) (p.compContinuousLinearMap L) 0 := by
    apply HasFPowerSeriesAt.compContinuousLinearMap
    simpa using hp
  filter_upwards [hpL.eventually_hasSum] with c hc
  have hterm (n : ℕ) : (p.compContinuousLinearMap L) n (fun _ => c) = 0 := by
    change (p n).toMultilinearMap (fun _ => c • z) = 0
    rw [(p n).toMultilinearMap.map_smul_univ (fun _ => c) (fun _ => z)]
    simp [hz n]
  simpa [hterm, L] using hc.unique (show HasSum
    (fun n => (p.compContinuousLinearMap L) n (fun _ => c)) 0 by
      simpa only [hterm] using (hasSum_zero (α := ℂ) (β := ℕ)))

/-- A cone contains a point whenever it contains all sufficiently small
scalar multiples of that point. -/
theorem mem_of_eventually_smul_mem
    {S : Set E} (hcone : ∀ (c : ℂ) ⦃x : E⦄, x ∈ S → c • x ∈ S)
    {z : E} (hz : ∀ᶠ c : ℂ in 𝓝 0, c • z ∈ S) : z ∈ S := by
  have hz' : ∀ᶠ c : ℂ in 𝓝[≠] 0, c • z ∈ S :=
    hz.filter_mono nhdsWithin_le_nhds
  have hne : ∀ᶠ c : ℂ in 𝓝[≠] 0, c ≠ 0 := self_mem_nhdsWithin
  obtain ⟨c, hc, hcz⟩ := (hne.and hz').exists
  have hc0 : c ≠ 0 := hc
  simpa [smul_smul, hc0] using hcone c⁻¹ hcz

/-- The polynomial obtained by restricting a multilinear form to its diagonal. -/
def diagonalPolynomial {d k : ℕ} (T : (Fin d → ℂ) [×k]→L[ℂ] ℂ) :
    MvPolynomial (Fin d) ℂ :=
  ∑ a : Fin k → Fin d,
    MvPolynomial.C (T (fun i => Pi.single (a i) 1)) *
      ∏ i : Fin k, MvPolynomial.X (a i)

/-- Evaluation of the diagonal polynomial recovers the multilinear form. -/
theorem eval_diagonalPolynomial {d k : ℕ}
    (T : (Fin d → ℂ) [×k]→L[ℂ] ℂ) (z : Fin d → ℂ) :
    MvPolynomial.eval z (diagonalPolynomial T) = T (fun _ => z) := by
  have hsum : (∑ j : Fin d, z j • Pi.single j (1 : ℂ)) = z := by
    ext i
    simp [Pi.smul_apply, Pi.single_apply]
  have h := T.toMultilinearMap.map_sum (fun (_ : Fin k) (j : Fin d) =>
    z j • Pi.single j (1 : ℂ))
  rw [hsum] at h
  simpa [diagonalPolynomial, MultilinearMap.map_smul_univ, smul_eq_mul,
    mul_comm] using h.symm

/-- Its homogeneous degree is exactly the arity of the multilinear form. -/
theorem diagonalPolynomial_isHomogeneous {d k : ℕ}
    (T : (Fin d → ℂ) [×k]→L[ℂ] ℂ) :
    (diagonalPolynomial T).IsHomogeneous k := by
  apply MvPolynomial.IsHomogeneous.sum
  intro a _
  apply MvPolynomial.IsHomogeneous.C_mul
  simpa using MvPolynomial.IsHomogeneous.prod Finset.univ
    (fun i : Fin k => MvPolynomial.X (R := ℂ) (a i)) (fun _ => 1)
    (fun i _ => MvPolynomial.isHomogeneous_X ℂ (a i))

/-- A cone defined by finitely many analytic equations near its vertex is
globally the common zero locus of the homogeneous Taylor polynomials. -/
theorem equations_from_analytic_vertex
    {d m : ℕ} {S : Set (Fin d → ℂ)}
    (hcone : ∀ (c : ℂ) ⦃x : Fin d → ℂ⦄, x ∈ S → c • x ∈ S)
    (f : Fin m → (Fin d → ℂ) → ℂ)
    (hf : ∀ i, AnalyticAt ℂ (f i) 0)
    (hS : ∀ᶠ x in 𝓝 0, x ∈ S ↔ ∀ i, f i x = 0) :
    ∃ P : Fin m × ℕ → MvPolynomial (Fin d) ℂ,
      (∀ i, (P i).IsHomogeneous i.2) ∧
      S = {z | ∀ i, MvPolynomial.eval z (P i) = 0} := by
  choose p hp using hf
  refine ⟨fun i => diagonalPolynomial (p i.1 i.2),
    fun i => diagonalPolynomial_isHomogeneous _, ?_⟩
  ext z
  constructor
  · intro hz i
    rw [eval_diagonalPolynomial]
    apply coefficient_vanishes hcone (hp i.1) _ hz
    filter_upwards [hS] with x hx
    exact fun h => (hx.mp h) i.1
  · intro hz
    apply mem_of_eventually_smul_mem hcone
    have heq : ∀ i, ∀ᶠ c : ℂ in 𝓝 0, f i (c • z) = 0 := by
      intro i
      apply eventually_smul_eq_zero (hp i)
      intro n
      simpa only [eval_diagonalPolynomial] using hz (i, n)
    have hscale : Tendsto (fun c : ℂ => c • z) (𝓝 0) (𝓝 0) := by
      have hcont : Continuous (fun c : ℂ => c • z) := continuous_id.smul continuous_const
      simpa only [zero_smul] using hcont.continuousAt.tendsto (x := (0 : ℂ))
    filter_upwards [hscale.eventually hS, Filter.eventually_all.mpr heq] with c hc he
    exact hc.mpr he

/-- An arbitrary collection of homogeneous polynomial equations in finitely
many variables has the same zero locus as a finite subcollection. -/
theorem finite_homogeneous_equations {d : ℕ} {ι : Type*}
    (P : ι → MvPolynomial (Fin d) ℂ)
    (hP : ∀ i, ∃ n, (P i).IsHomogeneous n) :
    ∃ Q : Finset (MvPolynomial (Fin d) ℂ),
      (∀ q ∈ Q, ∃ n, q.IsHomogeneous n) ∧
      ∀ z, (∀ q ∈ Q, MvPolynomial.eval z q = 0) ↔
        ∀ i, MvPolynomial.eval z (P i) = 0 := by
  classical
  obtain ⟨Q, hQ, hspan⟩ :=
    (Submodule.fg_span_iff_fg_span_finset_subset
      (R := MvPolynomial (Fin d) ℂ) (Set.range P)).mp
        (IsNoetherian.noetherian _)
  change Ideal.span (Set.range P) = Ideal.span (Q : Set (MvPolynomial (Fin d) ℂ)) at hspan
  refine ⟨Q, ?_, ?_⟩
  · intro q hq
    obtain ⟨i, rfl⟩ := hQ hq
    exact hP i
  · intro z
    constructor
    · intro hz i
      have hker : Ideal.span (Q : Set (MvPolynomial (Fin d) ℂ)) ≤
          RingHom.ker (MvPolynomial.eval z) := by
        apply Ideal.span_le.mpr
        intro q hq
        exact hz q hq
      apply hker
      rw [← hspan]
      exact Ideal.subset_span (Set.mem_range_self i)
    · intro hz q hq
      obtain ⟨i, rfl⟩ := hQ hq
      exact hz i

/-- Local analyticity at the vertex of a complex cone gives finitely many
global homogeneous polynomial equations defining the cone exactly. -/
theorem finite_equations_from_analytic_vertex
    {d m : ℕ} {S : Set (Fin d → ℂ)}
    (hcone : ∀ (c : ℂ) ⦃x : Fin d → ℂ⦄, x ∈ S → c • x ∈ S)
    (f : Fin m → (Fin d → ℂ) → ℂ)
    (hf : ∀ i, AnalyticAt ℂ (f i) 0)
    (hS : ∀ᶠ x in 𝓝 0, x ∈ S ↔ ∀ i, f i x = 0) :
    ∃ Q : Finset (MvPolynomial (Fin d) ℂ),
      (∀ q ∈ Q, ∃ n, q.IsHomogeneous n) ∧
      S = {z | ∀ q ∈ Q, MvPolynomial.eval z q = 0} := by
  obtain ⟨P, hP, hPS⟩ := equations_from_analytic_vertex hcone f hf hS
  obtain ⟨Q, hQ, hQP⟩ := finite_homogeneous_equations P (fun i => ⟨i.2, hP i⟩)
  refine ⟨Q, hQ, ?_⟩
  rw [hPS]
  ext z
  exact (hQP z).symm

end

end OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ConeEq.Constructions.Cone
