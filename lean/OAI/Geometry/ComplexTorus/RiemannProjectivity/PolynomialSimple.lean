import OAI.Geometry.ComplexTorus.RiemannProjectivity.ReducedFamiliesOn
import OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.WeierstrassPreparation

/-! # Polynomial Simple -/

namespace OAI

noncomputable section

namespace Geometry.ComplexTorus.RiemannProjectivity.PolynomialSimple.Constructions.PolynomialUnitFactor

/-! # RiemannProjectivity: simple roots descend through local holomorphic factorization -/

open _root_.Polynomial Filter
open scoped _root_.Topology

theorem derivative_eq {p q : ℂ[X]} {u : ℂ → ℂ} {z : ℂ}
    (hu : DifferentiableAt ℂ u z)
    (heq : (fun w => p.eval w) =ᶠ[𝓝 z] (fun w => q.eval w * u w))
    (hq : q.eval z = 0) : p.derivative.eval z = q.derivative.eval z * u z := by
  have hd := ((q.hasDerivAt z).mul hu.hasDerivAt).congr_of_eventuallyEq heq
  simpa only [hq, zero_mul, add_zero] using (p.hasDerivAt z).unique hd

theorem separable_of_local_factors {p q : ℂ[X]} (hp : p.Separable)
    (hfactor : ∀ z, q.eval z = 0 → ∃ u : ℂ → ℂ, DifferentiableAt ℂ u z ∧
      (fun w => p.eval w) =ᶠ[𝓝 z] (fun w => q.eval w * u w)) : q.Separable := by
  rw [separable_def]
  apply (Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed (k := ℂ) ℂ q q.derivative).mpr
  intro z
  by_cases hq : q.eval z = 0
  · right
    change q.derivative.eval z ≠ 0
    obtain ⟨u, hu, heq⟩ := hfactor z hq
    have hpz : p.eval z = 0 := by rw [heq.eq_of_nhds, hq, zero_mul]
    have hpd : p.derivative.eval z ≠ 0 :=
      hp.eval₂_derivative_ne_zero (RingHom.id ℂ) hpz
    rw [derivative_eq hu heq hq] at hpd
    exact (mul_ne_zero_iff.mp hpd).1
  · left
    exact hq

end Geometry.ComplexTorus.RiemannProjectivity.PolynomialSimple.Constructions.PolynomialUnitFactor

namespace Geometry.ComplexTorus.RiemannProjectivity.PolynomialSimple.Constructions.SimpleBranch

/-!
# RiemannProjectivity: a single analytic branch is a simple root of the reduced family

Preparation preserves multiplicities. At a nearby separable fiber its
single root forces preparation degree one; the same degree at the original
fiber makes the polynomial's vertical derivative nonzero.
-/

open Set Filter _root_.Polynomial _root_.Metric
open scoped _root_.Topology

theorem derivative_ne_zero {n : ℕ} {P : (Fin n → ℂ) → ℂ[X]}
    {O : Set (Fin n → ℂ)} (hO : IsOpen O)
    (hP : DifferentiableOn ℂ (fun p : (Fin n → ℂ) × ℂ => (P p.1).eval p.2) (O ×ˢ univ))
    {x : Fin n → ℂ} (hx : x ∈ O) {c : ℂ} {R : ℝ} (hR : 0 < R)
    (g : (Fin n → ℂ) → ℂ) (hg : ∀ y ∈ O, g y ∈ ball c R)
    (hroot : ∀ y ∈ O, ∀ z ∈ closedBall c R, (P y).eval z = 0 ↔ z = g y)
    (hsep : ∃ᶠ y in 𝓝 x, (P y).Separable) : (P x).derivative.eval (g x) ≠ 0 := by
  have hn (z : ℂ) (hz : z ∈ sphere c R) : (P x).eval z ≠ 0 := by
    intro hpz
    have hzg := (hroot x hx z (sphere_subset_closedBall hz)).mp hpz
    exact (ne_of_lt (mem_ball.mp (hg x hx))) (hzg ▸ mem_sphere.mp hz)
  obtain ⟨m, U, Q, hU, hxU, hUO, _, hQ⟩ :=
    AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.WeierstrassPreparation.Constructions.Preparation.exists_polynomial_preparation (hO.prod isOpen_univ) hP hR
      (fun _ _ => ⟨hx, mem_univ _⟩) hn
  have hsub : U ⊆ O := by
    intro y hy
    exact (hUO (show (y, c) ∈ U ×ˢ closedBall c R from ⟨hy, mem_closedBall_self hR.le⟩)).1
  have hiff (y : Fin n → ℂ) (hy : y ∈ U) (z : ℂ) (hz : z ∈ closedBall c R) :
      (P y).eval z = 0 ↔ (Q y).eval z = 0 := by
    obtain ⟨_, _, _, u, _, hun, hfu⟩ := hQ y hy
    rw [(hfu z hz).eq_of_nhds, mul_eq_zero, or_iff_left (hun z hz)]
  have hQg (y : Fin n → ℂ) (hy : y ∈ U) : (Q y).eval (g y) = 0 :=
    (hiff y hy (g y) (ball_subset_closedBall (hg y (hsub hy)))).mp
      ((hroot y (hsub hy) (g y) (ball_subset_closedBall (hg y (hsub hy)))).mpr rfl)
  have hQroots (y : Fin n → ℂ) (hy : y ∈ U) :
      {z : ℂ | (Q y).eval z = 0} = {g y} := by
    ext z
    constructor
    · intro hz
      have hzball := (hQ y hy).2.2.1 z hz
      exact (hroot y (hsub hy) z (ball_subset_closedBall hzball)).mp
        ((hiff y hy z (ball_subset_closedBall hzball)).mpr hz)
    · intro hz
      exact hz ▸ hQg y hy
  obtain ⟨y, hys, hyU⟩ := (hsep.and_eventually (hU.mem_nhds hxU)).exists
  have hQs : (Q y).Separable := by
    apply PolynomialUnitFactor.separable_of_local_factors hys
    intro z hz
    obtain ⟨_, _, hball, u, hu, _, hfu⟩ := hQ y hyU
    have hzclosed := ball_subset_closedBall (hball z hz)
    exact ⟨u, (hu z hzclosed).differentiableAt, hfu z hzclosed⟩
  have hm : m = 1 := by
    have h := AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.MonicRoots.Constructions.RootPolynomials.ncard_zero_set (hQ y hyU).1.ne_zero hQs
    rw [hQroots y hyU, ncard_singleton, (hQ y hyU).2.1] at h
    exact h.symm
  obtain ⟨hQm, hQd, _, u, hu, hun, hfu⟩ := hQ x hxU
  have hlinear : Q x = X - C (g x) :=
    eq_of_monic_of_dvd_of_natDegree_le (monic_X_sub_C _) hQm
      (dvd_iff_isRoot.mpr (hQg x hxU)) (by rw [hQd, hm, natDegree_X_sub_C])
  have hgclosed := ball_subset_closedBall (hg x hx)
  have hder := PolynomialUnitFactor.derivative_eq (p := P x) (hu (g x) hgclosed).differentiableAt
    (hfu (g x) hgclosed) (hQg x hxU)
  rw [hlinear, derivative_X_sub_C, eval_one, one_mul] at hder
  rw [hder]
  exact hun (g x) hgclosed

end Geometry.ComplexTorus.RiemannProjectivity.PolynomialSimple.Constructions.SimpleBranch

namespace Geometry.ComplexTorus.RiemannProjectivity.PolynomialSimple.Constructions.LocalCoordinateGraph

/-!
# RiemannProjectivity: a separating coordinate isolates one local projection branch

A closed map and a finite fiber keep all other sheets away from a small
vertical disk. A local inverse then describes the entire coordinate image
in that disk as one graph.
-/

open Set Filter _root_.Metric
open scoped _root_.Topology

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

theorem exists_graph {f : X → Y} (hf : IsClosedMap f) {l : X → ℂ} (hl : Continuous l)
    (e : OpenPartialHomeomorph X Y) (he : (e : X → Y) = f) {x : X} (hx : x ∈ e.source)
    (hfinite : (f ⁻¹' {f x}).Finite)
    (hsep : ∀ u, f u = f x → l u = l x → u = x) :
    ∃ (R : ℝ) (O : Set Y) (g : Y → ℂ), 0 < R ∧ IsOpen O ∧ f x ∈ O ∧
      ContinuousOn g O ∧ (∀ y ∈ O, g y ∈ ball (l x) R) ∧
      ∀ y ∈ O, ∀ z ∈ closedBall (l x) R,
        (y, z) ∈ range (fun u => (f u, l u)) ↔ z = g y := by
  let K := f ⁻¹' {f x} ∩ e.sourceᶜ
  let M := l '' K
  have hM : IsClosed M := ((hfinite.subset inter_subset_left).image l).isClosed
  have hxM : l x ∉ M := by
    rintro ⟨u, hu, hul⟩
    exact hu.2 ((hsep u hu.1 hul) ▸ hx)
  obtain ⟨R, hR, hRM⟩ := nhds_basis_closedBall.mem_iff.mp (hM.isOpen_compl.mem_nhds hxM)
  let D := e.sourceᶜ ∩ l ⁻¹' closedBall (l x) R
  have hD : IsClosed D := e.open_source.isClosed_compl.inter (isClosed_closedBall.preimage hl)
  have hbad : IsClosed (f '' D) := hf D hD
  have hxnot : f x ∉ f '' D := by
    rintro ⟨u, hu, huf⟩
    exact hRM hu.2 ⟨u, ⟨huf, hu.1⟩, rfl⟩
  have hfx : f x ∈ e.target := by rw [← he]; exact e.map_source hx
  let g : Y → ℂ := fun y => l (e.symm y)
  have hg : ContinuousOn g e.target := hl.comp_continuousOn e.continuousOn_symm
  have hgf : g (f x) = l x := by change l (e.symm (f x)) = l x; rw [← he, e.left_inv hx]
  let O₀ := e.target ∩ (f '' D)ᶜ
  have hO₀ : IsOpen O₀ := e.open_target.inter hbad.isOpen_compl
  let O := O₀ ∩ g ⁻¹' ball (l x) R
  have hO : IsOpen O := (hg.mono inter_subset_left).isOpen_inter_preimage hO₀ isOpen_ball
  refine ⟨R, O, g, hR, hO, ⟨⟨hfx, hxnot⟩, ?_⟩,
    hg.mono (fun _ hy => hy.1.1), fun _ hy => hy.2, ?_⟩
  · change g (f x) ∈ ball (l x) R
    rw [hgf]
    exact mem_ball_self hR
  · intro y hy z hz
    constructor
    · rintro ⟨u, hup⟩
      have huf : f u = y := congrArg Prod.fst hup
      have hul : l u = z := congrArg Prod.snd hup
      have hu : u ∈ e.source := by
        by_contra hnot
        exact hy.1.2 ⟨u, ⟨hnot, by change l u ∈ closedBall (l x) R; rwa [hul]⟩, huf⟩
      have hinv : e.symm (f u) = u := by rw [← he]; exact e.left_inv hu
      change z = l (e.symm y)
      rw [← huf, hinv, hul]
    · intro hzgy
      refine ⟨e.symm y, Prod.ext ?_ ?_⟩
      · rw [← he]
        exact e.right_inv hy.1.1
      · exact hzgy.symm

end Geometry.ComplexTorus.RiemannProjectivity.PolynomialSimple.Constructions.LocalCoordinateGraph

end

end OAI
