import OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProperFiberPolynomial
import OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.CoefficientExtension

/-! # Global Fiber Polynomial -/

namespace OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.GlobalFiberPolynomial.Constructions.Cone

noncomputable section

/-!
# Gluing reduced equations of proper finite fibers

The reduced local polynomials agree on overlaps, since they have the same
generic simple roots. Their coefficients consequently define a global
holomorphic polynomial family on any open part of the base where the fibers
are finite and the total set is locally analytic along them.
-/

open Set Filter _root_.Polynomial
open scoped _root_.Topology

theorem nonzero_germ_of_dense_nonzero
    {E : Type*} [TopologicalSpace E] {c : E → ℂ} {U : Set E}
    (hdense : U ⊆ closure {y | y ∈ U ∧ c y ≠ 0}) {x : E} (hx : x ∈ U) :
    ¬∀ᶠ y in 𝓝 x, c y = 0 := by
  intro hz
  obtain ⟨y, hy, hzy⟩ := ((mem_closure_iff_frequently.mp (hdense hx)).and_eventually hz).exists
  exact hy.2 hzy

theorem reduced_fiber_polynomials_eq_on_overlap {n : ℕ}
    {S : Set ((Fin n → ℂ) × ℂ)}
    {P Q : (Fin n → ℂ) → ℂ[X]} {c d : (Fin n → ℂ) → ℂ}
    {U V : Set (Fin n → ℂ)} (hU : IsOpen U) (hV : IsOpen V)
    (hc : DifferentiableOn ℂ c U) (hd : DifferentiableOn ℂ d V)
    (hcdense : U ⊆ closure {y | y ∈ U ∧ c y ≠ 0})
    (hddense : V ⊆ closure {y | y ∈ V ∧ d y ≠ 0})
    (hPcoeff : ∀ j, DifferentiableOn ℂ (fun y => (P y).coeff j) U)
    (hQcoeff : ∀ j, DifferentiableOn ℂ (fun y => (Q y).coeff j) V)
    (hP : ∀ y ∈ U, (P y).Monic) (hQ : ∀ y ∈ V, (Q y).Monic)
    (hProots : ∀ y ∈ U, c y ≠ 0 → (P y).Separable ∧
      ∀ z : ℂ, (y, z) ∈ S ↔ (P y).eval z = 0)
    (hQroots : ∀ y ∈ V, d y ≠ 0 → (Q y).Separable ∧
      ∀ z : ℂ, (y, z) ∈ S ↔ (Q y).eval z = 0) :
    EqOn P Q (U ∩ V) := by
  intro y hy
  apply Filter.EventuallyEq.eq_of_nhds
  apply CoefficientExtension.Constructions.GenericPolynomial.eventually_eq_of_generic_roots (hU.inter hV) hy
    (hc.mono inter_subset_left) (hd.mono inter_subset_right)
    (nonzero_germ_of_dense_nonzero hcdense hy.1) (nonzero_germ_of_dense_nonzero hddense hy.2)
    (fun j => (hPcoeff j).continuousOn.mono inter_subset_left)
    (fun j => (hQcoeff j).continuousOn.mono inter_subset_right)
  intro z hz hcz hdz
  exact ⟨hP z hz.1, hQ z hz.2, (hProots z hz.1 hcz).1, (hQroots z hz.2 hdz).1,
    fun w => ((hProots z hz.1 hcz).2 w).symm.trans ((hQroots z hz.2 hdz).2 w)⟩

theorem exists_global_reduced_fiber_polynomial {n : ℕ}
    {S : Set ((Fin n → ℂ) × ℂ)} {Ω : Set (Fin n → ℂ)} (hΩ : IsOpen Ω)
    (hproper : IsProperMap (fun p : S => p.val.1))
    (hfinite : ∀ x ∈ Ω, {z : ℂ | (x, z) ∈ S}.Finite)
    (hlocal : ∀ x ∈ Ω, ∀ z, (x, z) ∈ S → ZeroLocus.Constructions.Cone.HolomorphicZeroSetAt S (x, z)) :
    ∃ P : (Fin n → ℂ) → ℂ[X],
      (∀ j, DifferentiableOn ℂ (fun y => (P y).coeff j) Ω) ∧
      (∀ y ∈ Ω, (P y).Monic) ∧
      ∀ x ∈ Ω, ∃ (d : ℕ) (V : Set (Fin n → ℂ)) (c : (Fin n → ℂ) → ℂ),
        IsOpen V ∧ x ∈ V ∧ V ⊆ Ω ∧ DifferentiableOn ℂ c V ∧
        (¬∀ᶠ y in 𝓝 x, c y = 0) ∧ V ⊆ closure {y | y ∈ V ∧ c y ≠ 0} ∧
        (∀ y ∈ V, (P y).natDegree = d) ∧
        ∀ y ∈ V, c y ≠ 0 → (P y).Separable ∧
          ∀ z : ℂ, (y, z) ∈ S ↔ (P y).eval z = 0 := by
  classical
  have hex (a : Ω) := ProperFiberPolynomial.Constructions.Cone.exists_reduced_full_fiber_polynomial hproper
    (hfinite a a.property) (hlocal a a.property)
  choose d U Q c hU hxU hc hcn hdense hcoeff hQ hroot using hex
  have hoverlap (a b : Ω) : EqOn (Q a) (Q b) (U a ∩ U b) :=
    reduced_fiber_polynomials_eq_on_overlap (hU a) (hU b) (hc a) (hc b)
      (hdense a) (hdense b) (hcoeff a) (hcoeff b)
      (fun y hy => (hQ a y hy).1) (fun y hy => (hQ b y hy).1) (hroot a) (hroot b)
  let P : (Fin n → ℂ) → ℂ[X] := fun y => if hy : y ∈ Ω then Q ⟨y, hy⟩ y else 0
  have hPQ (a : Ω) (y : Fin n → ℂ) (hy : y ∈ U a) (hyΩ : y ∈ Ω) : P y = Q a y := by
    rw [show P y = Q ⟨y, hyΩ⟩ y from dite_eq_left hyΩ]
    exact hoverlap ⟨y, hyΩ⟩ a ⟨hxU ⟨y, hyΩ⟩, hy⟩
  refine ⟨P, ?_, ?_, ?_⟩
  · intro j y hy
    let a : Ω := ⟨y, hy⟩
    have heq : (fun z => (P z).coeff j) =ᶠ[𝓝 y] (fun z => (Q a z).coeff j) := by
      filter_upwards [(hU a).mem_nhds (hxU a), hΩ.mem_nhds hy] with z hz hzΩ
      rw [hPQ a z hz hzΩ]
    exact (((hcoeff a j).differentiableAt ((hU a).mem_nhds (hxU a))).congr_of_eventuallyEq heq).differentiableWithinAt
  · intro y hy
    rw [hPQ ⟨y, hy⟩ y (hxU ⟨y, hy⟩) hy]
    exact (hQ ⟨y, hy⟩ y (hxU ⟨y, hy⟩)).1
  · intro x hx
    let a : Ω := ⟨x, hx⟩
    refine ⟨d a, U a ∩ Ω, c a, (hU a).inter hΩ, ⟨hxU a, hx⟩, inter_subset_right,
      (hc a).mono inter_subset_left, hcn a, ?_, ?_, ?_⟩
    · intro y hy
      apply mem_closure_iff_frequently.mpr
      apply ((mem_closure_iff_frequently.mp (hdense a hy.1)).and_eventually (hΩ.mem_nhds hy.2)).mono
      intro z hz
      exact ⟨⟨hz.1.1, hz.2⟩, hz.1.2⟩
    · intro y hy
      rw [hPQ a y hy.1 hy.2]
      exact (hQ a y hy.1).2
    · intro y hy hcy
      rw [hPQ a y hy.1 hy.2]
      exact hroot a y hy.1 hcy

theorem exists_constant_degree_of_locally_constant
    {E : Type*} [TopologicalSpace E] {Ω : Set E} (hΩ : IsPreconnected Ω) (hne : Ω.Nonempty)
    {P : E → ℂ[X]}
    (hdeg : ∀ x ∈ Ω, ∃ d : ℕ, ∃ V : Set E, IsOpen V ∧ x ∈ V ∧
      ∀ y ∈ V, (P y).natDegree = d) :
    ∃ d : ℕ, ∀ y ∈ Ω, (P y).natDegree = d := by
  have hcont : ContinuousOn (fun y => (P y).natDegree) Ω := by
    intro x hx
    obtain ⟨d, V, hV, hxV, hVdeg⟩ := hdeg x hx
    have heq : (fun y => (P y).natDegree) =ᶠ[𝓝 x] (fun _ => d) := by
      filter_upwards [hV.mem_nhds hxV] with y hy
      exact hVdeg y hy
    have ht : Tendsto (fun y => (P y).natDegree) (𝓝 x) (𝓝 d) :=
      tendsto_const_nhds.congr' heq.symm
    have hc : ContinuousAt (fun y => (P y).natDegree) x := by
      change Tendsto (fun y => (P y).natDegree) (𝓝 x) (𝓝 (P x).natDegree)
      simpa only [hVdeg x hxV] using ht
    exact hc.continuousWithinAt
  obtain ⟨x, hx⟩ := hne
  exact ⟨(P x).natDegree, fun y hy => (hΩ.constant hcont hx hy).symm⟩

theorem exists_global_fixed_degree_fiber_polynomial {n : ℕ}
    {S : Set ((Fin n → ℂ) × ℂ)} {Ω : Set (Fin n → ℂ)} (hΩ : IsOpen Ω)
    (hconnected : IsPreconnected Ω) (hne : Ω.Nonempty)
    (hproper : IsProperMap (fun p : S => p.val.1))
    (hfinite : ∀ x ∈ Ω, {z : ℂ | (x, z) ∈ S}.Finite)
    (hlocal : ∀ x ∈ Ω, ∀ z, (x, z) ∈ S → ZeroLocus.Constructions.Cone.HolomorphicZeroSetAt S (x, z)) :
    ∃ (d : ℕ) (P : (Fin n → ℂ) → ℂ[X]),
      (∀ j, DifferentiableOn ℂ (fun y => (P y).coeff j) Ω) ∧
      (∀ y ∈ Ω, (P y).Monic ∧ (P y).natDegree = d) ∧
      ∀ x ∈ Ω, ∃ (V : Set (Fin n → ℂ)) (c : (Fin n → ℂ) → ℂ),
        IsOpen V ∧ x ∈ V ∧ V ⊆ Ω ∧ DifferentiableOn ℂ c V ∧
        (¬∀ᶠ y in 𝓝 x, c y = 0) ∧ V ⊆ closure {y | y ∈ V ∧ c y ≠ 0} ∧
        ∀ y ∈ V, c y ≠ 0 → (P y).Separable ∧
          ∀ z : ℂ, (y, z) ∈ S ↔ (P y).eval z = 0 := by
  obtain ⟨P, hcoeff, hP, hnear⟩ := exists_global_reduced_fiber_polynomial hΩ hproper hfinite hlocal
  have hlocdeg (x : Fin n → ℂ) (hx : x ∈ Ω) :
      ∃ d : ℕ, ∃ V : Set (Fin n → ℂ), IsOpen V ∧ x ∈ V ∧
        ∀ y ∈ V, (P y).natDegree = d := by
    obtain ⟨d, V, _, hV, hxV, _, _, _, _, hdeg, _⟩ := hnear x hx
    exact ⟨d, V, hV, hxV, hdeg⟩
  obtain ⟨d, hdeg⟩ := exists_constant_degree_of_locally_constant hconnected hne hlocdeg
  refine ⟨d, P, hcoeff, fun y hy => ⟨hP y hy, hdeg y hy⟩, ?_⟩
  intro x hx
  obtain ⟨_, V, c, hV, hxV, hVΩ, hc, hcn, hdense, _, hroot⟩ := hnear x hx
  exact ⟨V, c, hV, hxV, hVΩ, hc, hcn, hdense, hroot⟩

end

end OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.GlobalFiberPolynomial.Constructions.Cone
