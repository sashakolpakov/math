import OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.PolynomialProducts
import OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.FiberCardinality

/-! # Proper Fiber Polynomial -/

namespace OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProperFiberPolynomial.Constructions.Cone

noncomputable section

/-!
# A holomorphic polynomial for a full generic proper fiber

Multiply the extended local disk equations for the finitely many points in
the reference fiber. Properness ensures the disks cover all nearby fibers.
Their product therefore describes the full fiber off one exceptional set.
-/

open Set Filter _root_.Metric _root_.Polynomial
open scoped _root_.Topology

theorem exists_generic_full_fiber_polynomial {n : ℕ}
    {S : Set ((Fin n → ℂ) × ℂ)} {x : Fin n → ℂ}
    (hproper : IsProperMap (fun p : S => p.val.1))
    (hfinite : {z : ℂ | (x, z) ∈ S}.Finite)
    (hlocal : ∀ z, (x, z) ∈ S → ZeroLocus.Constructions.Cone.HolomorphicZeroSetAt S (x, z)) :
    ∃ (d : ℕ) (V : Set (Fin n → ℂ)) (P : (Fin n → ℂ) → ℂ[X])
        (c : (Fin n → ℂ) → ℂ) (M : ℝ),
      IsOpen V ∧ x ∈ V ∧ DifferentiableOn ℂ c V ∧ (¬∀ᶠ y in 𝓝 x, c y = 0) ∧
      (∀ j, DifferentiableOn ℂ (fun y => (P y).coeff j) V) ∧
      (∀ y ∈ V, (P y).Monic ∧ (P y).natDegree = d) ∧
      ∀ y ∈ V, c y ≠ 0 →
        (∀ z : ℂ, (y, z) ∈ S ↔ (P y).eval z = 0) ∧
        ∀ z : ℂ, (P y).eval z = 0 → ‖z‖ ≤ M := by
  classical
  let K := {z : ℂ | (x, z) ∈ S}
  let : Fintype K := hfinite.fintype
  have hprep := fun a : K => ExtendedFibers.Constructions.Preparation.extended_monic_equation_of_finite_fiber
    (hlocal a a.property) hfinite
  choose R d U P c hR hU hx hc hdense hcoeff hmonic hroot using hprep
  let Z := ⋂ a : K, U a
  have hZ : IsOpen Z := isOpen_iInter_of_finite hU
  have hxZ : x ∈ Z := mem_iInter.mpr hx
  have hZU (a : K) : Z ⊆ U a := iInter_subset U a
  have hcn (a : K) : ¬∀ᶠ y in 𝓝 x, c a y = 0 := by
    intro hz
    obtain ⟨y, hy, hzy⟩ :=
      ((mem_closure_iff_frequently.mp (hdense a (hx a))).and_eventually hz).exists
    exact hy.2 hzy
  let C : (Fin n → ℂ) → ℂ := fun y => ∏ a : K, c a y
  let Q : (Fin n → ℂ) → ℂ[X] := fun y => ∏ a : K, P a y
  have hC : DifferentiableOn ℂ C Z := AnalyticElimination.Constructions.Elimination.differentiableOn_finset_product Finset.univ
    (fun a _ => (hc a).mono (hZU a))
  have hCn : ¬∀ᶠ y in 𝓝 x, C y = 0 := PolynomialProducts.Constructions.GenericPolynomial.not_eventually_zero_prod c hZ hxZ
    (fun a => (hc a).mono (hZU a)) hcn Finset.univ
  obtain ⟨W, hWsub, hW, hxW⟩ := _root_.mem_nhds_iff.mp
    (FiberCardinality.Constructions.Cone.eventually_fiber_mem_disk_union hproper R hR)
  let V := Z ∩ W
  let M : ℝ := ∑ a : K, (‖(a : ℂ)‖ + R a)
  have hQa (y : Fin n → ℂ) (hy : y ∈ V) (a : K) := hmonic a y (hZU a hy.1)
  refine ⟨∑ a : K, d a, V, Q, C, M, hZ.inter hW, ⟨hxZ, hxW⟩,
    hC.mono inter_subset_left, hCn, ?_, ?_, ?_⟩
  · intro j
    exact (PolynomialProducts.Constructions.GenericPolynomial.differentiableOn_coeff_prod P
      (fun a i => (hcoeff a i).mono (hZU a)) Finset.univ j).mono inter_subset_left
  · intro y hy
    constructor
    · exact monic_prod_of_monic _ _ (fun a _ => (hQa y hy a).1)
    · change (∏ a : K, P a y).natDegree = _
      rw [natDegree_prod_of_monic _ _ (fun a _ => (hQa y hy a).1)]
      exact Finset.sum_congr rfl (fun a _ => (hQa y hy a).2)
  · intro y hy hCy
    have hca (a : K) : c a y ≠ 0 := Finset.prod_ne_zero_iff.mp hCy a (Finset.mem_univ _)
    have hroots (a : K) := hroot a y (hZU a hy.1) (hca a)
    have heval (z : ℂ) : (Q y).eval z = 0 ↔ ∃ a : K, (P a y).eval z = 0 := by
      simp only [Q, eval_prod, Finset.prod_eq_zero_iff, Finset.mem_univ, true_and]
    constructor
    · intro z
      rw [heval]
      constructor
      · intro hzs
        obtain ⟨a, ha⟩ := hWsub hy.2 z hzs
        exact ⟨a, ((hroots a).2.2 z (ball_subset_closedBall ha)).mp hzs⟩
      · rintro ⟨a, ha⟩
        exact ((hroots a).2.2 z (ball_subset_closedBall ((hroots a).2.1 z ha))).mpr ha
    · intro z hz
      obtain ⟨a, ha⟩ := (heval z).mp hz
      have hdist := mem_ball_iff_norm.mp ((hroots a).2.1 z ha)
      have hzbound : ‖z‖ ≤ ‖(a : ℂ)‖ + R a := by
        have hnorm := norm_le_norm_sub_add z (a : ℂ)
        linarith
      apply hzbound.trans
      exact Finset.single_le_sum (fun b _ => add_nonneg (norm_nonneg _) (hR b).le)
        (Finset.mem_univ a)

/-- The full generic fiber has a reduced monic equation with coefficients
holomorphic throughout the base neighborhood. -/
theorem exists_reduced_full_fiber_polynomial {n : ℕ}
    {S : Set ((Fin n → ℂ) × ℂ)} {x : Fin n → ℂ}
    (hproper : IsProperMap (fun p : S => p.val.1))
    (hfinite : {z : ℂ | (x, z) ∈ S}.Finite)
    (hlocal : ∀ z, (x, z) ∈ S → ZeroLocus.Constructions.Cone.HolomorphicZeroSetAt S (x, z)) :
    ∃ (d : ℕ) (V : Set (Fin n → ℂ)) (P : (Fin n → ℂ) → ℂ[X])
        (c : (Fin n → ℂ) → ℂ),
      IsOpen V ∧ x ∈ V ∧ DifferentiableOn ℂ c V ∧ (¬∀ᶠ y in 𝓝 x, c y = 0) ∧
      V ⊆ closure {y | y ∈ V ∧ c y ≠ 0} ∧
      (∀ j, DifferentiableOn ℂ (fun y => (P y).coeff j) V) ∧
      (∀ y ∈ V, (P y).Monic ∧ (P y).natDegree = d) ∧
      ∀ y ∈ V, c y ≠ 0 → (P y).Separable ∧
        ∀ z : ℂ, (y, z) ∈ S ↔ (P y).eval z = 0 := by
  obtain ⟨d, U, P, c₀, M, hU, hxU, hc₀, hc₀n, hPcoeff, hP, hroots⟩ :=
    exists_generic_full_fiber_polynomial hproper hfinite hlocal
  obtain ⟨k, Q, c₁, W, hW, hxW, hWU, hc₁, hc₁n, hQcoeff, hQ⟩ :=
    SquarefreeFamilies.Constructions.GenericPolynomial.exists_monic_separable_common_root_family (fun _ : Unit => P)
      hU hxU d (fun _ => hPcoeff) (fun _ y hy => (hP y hy).2.le)
      (fun y hy => ⟨(), (hP y hy).1.ne_zero⟩)
  let c : (Fin n → ℂ) → ℂ := fun y => c₀ y * c₁ y
  have hc : DifferentiableOn ℂ c W := (hc₀.mono hWU).fun_mul hc₁
  have hcn : ¬∀ᶠ y in 𝓝 x, c y = 0 :=
    GenericDegree.Constructions.GenericPolynomial.not_eventually_zero_mul hW hxW (hc₀.mono hWU) hc₁ hc₀n hc₁n
  have hparts (y : Fin n → ℂ) (hy : c y ≠ 0) : c₀ y ≠ 0 ∧ c₁ y ≠ 0 := mul_ne_zero_iff.mp hy
  have hPQ (y : Fin n → ℂ) (hy : y ∈ W) (hcy : c y ≠ 0) (z : ℂ) :
      (P y).eval z = 0 ↔ (Q y).eval z = 0 := by
    simpa only [forall_const] using (hQ y hy (hparts y hcy).2).2.2.2 z
  have hcoeff : ∀ j, DifferentiableOn ℂ (fun y => (Q y).coeff j) {y | y ∈ W ∧ c y ≠ 0} :=
    fun j => (hQcoeff j).mono (fun y hy => ⟨hy.1, (hparts y hy.2).2⟩)
  have hmonic (y : Fin n → ℂ) (hy : y ∈ W) (hcy : c y ≠ 0) :
      (Q y).Monic ∧ (Q y).natDegree = k :=
    ⟨(hQ y hy (hparts y hcy).2).1, (hQ y hy (hparts y hcy).2).2.1⟩
  have hbound (j : ℕ) : ∃ C : ℝ, ∀ y ∈ W, c y ≠ 0 → ‖(Q y).coeff j‖ ≤ C := by
    refine ⟨(k.choose j : ℝ) * (max 1 M) ^ k, ?_⟩
    intro y hy hcy
    rw [← (hmonic y hy hcy).2]
    apply MonicRoots.Constructions.RootPolynomials.norm_coeff_le_of_roots_bounded (hmonic y hy hcy).1
    intro z hz
    exact (hroots y (hWU hy) (hparts y hcy).1).2 z ((hPQ y hy hcy z).mpr hz)
  obtain ⟨V, G, hV, hxV, hVW, hdense, hGcoeff, hG, hGQ⟩ :=
    CoefficientExtension.Constructions.GenericPolynomial.exists_extended_monic_family hW hc hcoeff hmonic hbound hxW hcn
  refine ⟨k, V, G, c, hV, hxV, hc.mono hVW, hcn, hdense, hGcoeff, hG, ?_⟩
  intro y hy hcy
  rw [hGQ y hy hcy]
  exact ⟨(hQ y (hVW hy) (hparts y hcy).2).2.2.1,
    fun z => ((hroots y (hWU (hVW hy)) (hparts y hcy).1).1 z).trans (hPQ y (hVW hy) hcy z)⟩

end

end OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProperFiberPolynomial.Constructions.Cone
