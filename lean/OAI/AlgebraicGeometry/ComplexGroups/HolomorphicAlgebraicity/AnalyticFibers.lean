import OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.Projection
import OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ZeroLocus
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Topology.Connected.Clopen
import Mathlib.Analysis.Complex.CauchyIntegral

/-! # Analytic Fibers -/

namespace OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity

noncomputable section

/-!
# Finiteness of analytic fibers in a complex line

A compact subset of a complex line, locally cut out by finitely many
holomorphic equations, is finite. The proof uses isolated zeros and
connectedness, rather than assuming a finiteness statement for analytic sets.
-/

open Set Filter _root_.Metric
open scoped _root_.Topology

/-- A local finite holomorphic zero-locus description in a complex line. -/
def AnalyticFibers.Constructions.Cone.LineAnalyticAt (S : Set ℂ) (x : ℂ) : Prop :=
  ∃ (m : ℕ) (f : Fin m → ℂ → ℂ), (∀ i, AnalyticAt ℂ (f i) x) ∧
    ∀ᶠ z in 𝓝 x, z ∈ S ↔ ∀ i, f i z = 0

/-- Accumulation forces all local equations to vanish identically. -/
theorem AnalyticFibers.Constructions.Cone.LineAnalyticAt.mem_interior_of_frequently {S : Set ℂ} {x : ℂ}
    (hlocal : AnalyticFibers.Constructions.Cone.LineAnalyticAt S x) (hfreq : ∃ᶠ z in 𝓝[≠] x, z ∈ S) :
    x ∈ interior S := by
  obtain ⟨m, f, hf, heq⟩ := hlocal
  have hzero (i : Fin m) : ∀ᶠ z in 𝓝 x, f i z = 0 := by
    apply (hf i).frequently_zero_iff_eventually_zero.mp
    exact (hfreq.and_eventually (heq.filter_mono nhdsWithin_le_nhds)).mono
      (fun z hz => (hz.2.mp hz.1) i)
  rw [mem_interior_iff_mem_nhds]
  filter_upwards [heq, eventually_all.mpr hzero] with z hz hzeros
  exact hz.mpr hzeros

/-- The interior of a closed locally analytic subset of a complex line is closed. -/
theorem AnalyticFibers.Constructions.Cone.isClosed_interior_of_lineAnalytic {S : Set ℂ} (hS : IsClosed S)
    (hlocal : ∀ x ∈ S, AnalyticFibers.Constructions.Cone.LineAnalyticAt S x) : IsClosed (interior S) := by
  apply isClosed_of_closure_subset
  intro x hx
  by_cases hi : x ∈ interior S
  · exact hi
  have hxS : x ∈ S := hS.closure_subset (closure_mono interior_subset hx)
  apply (hlocal x hxS).mem_interior_of_frequently
  rw [frequently_nhdsWithin_iff]
  exact (mem_closure_iff_frequently.mp hx).mono (fun z hz =>
    ⟨interior_subset hz, by
      simp only [mem_compl_iff, mem_singleton_iff]
      intro heq
      exact hi (heq ▸ hz)⟩)

/-- Compact local analytic subsets of the complex line are finite. -/
theorem AnalyticFibers.Constructions.Cone.finite_of_isCompact_lineAnalytic {S : Set ℂ} (hS : IsCompact S)
    (hlocal : ∀ x ∈ S, AnalyticFibers.Constructions.Cone.LineAnalyticAt S x) : S.Finite := by
  have hint : interior S = ∅ := by
    rcases isClopen_iff.mp
      (⟨AnalyticFibers.Constructions.Cone.isClosed_interior_of_lineAnalytic hS.isClosed hlocal,
        isOpen_interior⟩ : IsClopen (interior S)) with h | h
    · exact h
    · have hSuniv : S = univ := univ_subset_iff.mp (h ▸ interior_subset)
      exact False.elim (noncompact_univ ℂ (hSuniv ▸ hS))
  by_contra hinf
  obtain ⟨x, hx, hacc⟩ := exists_nhds_ne_inf_principal_neBot hS hinf
  have hfreq : ∃ᶠ z in 𝓝[≠] x, z ∈ S := frequently_iff_neBot.mpr hacc
  have hi := (hlocal x hx).mem_interior_of_frequently hfreq
  simp [hint] at hi

/-- An affine coordinate line is an analytic map of its complex coordinate. -/
theorem AnalyticFibers.Constructions.Cone.analyticAt_cons {n : ℕ} (y : Fin n → ℂ) (c : ℂ) :
    AnalyticAt ℂ (fun a : ℂ => (Fin.cons a y : Fin (n + 1) → ℂ)) c := by
  apply AnalyticAt.pi
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact analyticAt_id
  · exact analyticAt_const

/-- Restricting local holomorphic equations to a coordinate line gives
one-variable analytic equations by Cauchy's theorem. -/
theorem ZeroLocus.Constructions.Cone.HolomorphicZeroSetAt.coordinateFiber {n : ℕ}
    {S : Set (Fin (n + 1) → ℂ)} {y : Fin n → ℂ} {c : ℂ}
    (hlocal : ZeroLocus.Constructions.Cone.HolomorphicZeroSetAt S (Fin.cons c y)) :
    AnalyticFibers.Constructions.Cone.LineAnalyticAt {a : ℂ | Fin.cons a y ∈ S} c := by
  obtain ⟨U, hU, hcU, m, f, hf, heq⟩ := hlocal
  let line : ℂ → (Fin (n + 1) → ℂ) := fun a => Fin.cons a y
  have hline : Differentiable ℂ line := fun a => (AnalyticFibers.Constructions.Cone.analyticAt_cons y a).differentiableAt
  have hpre : line ⁻¹' U ∈ 𝓝 c := (hU.preimage hline.continuous).mem_nhds hcU
  refine ⟨m, (fun i a => f i (line a)), (fun i => ?_), ?_⟩
  · exact ((hf i).comp hline.differentiableOn (mapsTo_preimage line U)).analyticAt hpre
  · filter_upwards [hpre] with a ha
    exact heq (line a) ha

/-- The fibers of a coordinate projection of a closed cone are compact. -/
theorem AnalyticFibers.Constructions.Cone.isCompact_coordinateFiber {n : ℕ} {S : Set (Fin (n + 1) → ℂ)}
    (hS : IsClosed S)
    (hcone : ∀ (a : ℂ) ⦃x : Fin (n + 1) → ℂ⦄, x ∈ S → a • x ∈ S)
    (haxis : (Fin.cons 1 0 : Fin (n + 1) → ℂ) ∉ S) (y : Fin n → ℂ) :
    IsCompact {c : ℂ | Fin.cons c y ∈ S} := by
  obtain ⟨C, _, hbound⟩ := Projection.Constructions.Cone.norm_le_projection hS hcone (Projection.Constructions.Cone.tailProjection n)
    (Projection.Constructions.Cone.tailProjection_kernel_trivial hcone haxis)
  apply isCompact_iff_isClosed_bounded.mpr
  refine ⟨hS.preimage (continuous_iff_continuousAt.mpr
    (fun c => (AnalyticFibers.Constructions.Cone.analyticAt_cons y c).continuousAt)), ?_⟩
  apply isBounded_iff_forall_norm_le.mpr
  refine ⟨C * ‖y‖, fun c hc => ?_⟩
  have hnorm : ‖c‖ ≤ ‖(Fin.cons c y : Fin (n + 1) → ℂ)‖ :=
    norm_le_pi_norm (Fin.cons c y : Fin (n + 1) → ℂ) 0
  exact hnorm.trans (by simpa only [Projection.Constructions.Cone.tailProjection_cons] using hbound (Fin.cons c y) hc)

/-- Local analytic equations away from the vertex imply that every fiber of
the coordinate projection is finite. The fiber above zero uses the kernel
condition, so no analytic extension at the vertex is assumed here. -/
theorem AnalyticFibers.Constructions.Cone.finite_coordinateFiber {n : ℕ} {S : Set (Fin (n + 1) → ℂ)}
    (hS : IsClosed S)
    (hcone : ∀ (a : ℂ) ⦃x : Fin (n + 1) → ℂ⦄, x ∈ S → a • x ∈ S)
    (haxis : (Fin.cons 1 0 : Fin (n + 1) → ℂ) ∉ S)
    (hlocal : ∀ x ∈ S, x ≠ 0 →
      ∃ (m : ℕ) (f : Fin m → (Fin (n + 1) → ℂ) → ℂ),
        (∀ i, AnalyticAt ℂ (f i) x) ∧
        ∀ᶠ z in 𝓝 x, z ∈ S ↔ ∀ i, f i z = 0)
    (y : Fin n → ℂ) : {c : ℂ | Fin.cons c y ∈ S}.Finite := by
  by_cases hy : y = 0
  · subst y
    apply (finite_singleton (0 : ℂ)).subset
    intro c hc
    have hz := Projection.Constructions.Cone.tailProjection_kernel_trivial hcone haxis (Fin.cons c 0) hc
      (Projection.Constructions.Cone.tailProjection_cons c 0)
    simpa only [mem_singleton_iff, Fin.cons_zero, Pi.zero_apply] using congrFun hz 0
  · apply AnalyticFibers.Constructions.Cone.finite_of_isCompact_lineAnalytic (AnalyticFibers.Constructions.Cone.isCompact_coordinateFiber hS hcone haxis y)
    intro c hc
    have hnonzero : (Fin.cons c y : Fin (n + 1) → ℂ) ≠ 0 := by
      intro hz
      apply hy
      simpa only [Projection.Constructions.Cone.tailProjection_cons, map_zero] using congrArg (Projection.Constructions.Cone.tailProjection n) hz
    obtain ⟨m, f, hf, heq⟩ := hlocal (Fin.cons c y) hc hnonzero
    refine ⟨m, (fun i a => f i (Fin.cons a y)),
      (fun i => (hf i).comp (f := fun a : ℂ => (Fin.cons a y : Fin (n + 1) → ℂ))
        (AnalyticFibers.Constructions.Cone.analyticAt_cons y c)), ?_⟩
    exact (AnalyticFibers.Constructions.Cone.analyticAt_cons y c).continuousAt.tendsto.eventually heq

/-- Finite fibers follow from local complex differentiability, without any
multivariable analyticity theorem or analytic assumption at the vertex. -/
theorem AnalyticFibers.Constructions.Cone.finite_coordinateFiber_of_holomorphic {n : ℕ} {S : Set (Fin (n + 1) → ℂ)}
    (hS : IsClosed S)
    (hcone : ∀ (a : ℂ) ⦃x : Fin (n + 1) → ℂ⦄, x ∈ S → a • x ∈ S)
    (haxis : (Fin.cons 1 0 : Fin (n + 1) → ℂ) ∉ S)
    (hlocal : ∀ x ∈ S, x ≠ 0 → ZeroLocus.Constructions.Cone.HolomorphicZeroSetAt S x)
    (y : Fin n → ℂ) : {c : ℂ | Fin.cons c y ∈ S}.Finite := by
  by_cases hy : y = 0
  · subst y
    apply (finite_singleton (0 : ℂ)).subset
    intro c hc
    have hz := Projection.Constructions.Cone.tailProjection_kernel_trivial hcone haxis (Fin.cons c 0) hc
      (Projection.Constructions.Cone.tailProjection_cons c 0)
    simpa only [mem_singleton_iff, Fin.cons_zero, Pi.zero_apply] using congrFun hz 0
  · apply AnalyticFibers.Constructions.Cone.finite_of_isCompact_lineAnalytic (AnalyticFibers.Constructions.Cone.isCompact_coordinateFiber hS hcone haxis y)
    intro c hc
    have hnonzero : (Fin.cons c y : Fin (n + 1) → ℂ) ≠ 0 := by
      intro hz
      apply hy
      simpa only [Projection.Constructions.Cone.tailProjection_cons, map_zero] using congrArg (Projection.Constructions.Cone.tailProjection n) hz
    exact (hlocal _ hc hnonzero).coordinateFiber

end

end OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity
