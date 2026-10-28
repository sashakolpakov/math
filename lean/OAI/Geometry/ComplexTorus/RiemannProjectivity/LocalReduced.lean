import OAI.Geometry.ComplexTorus.RiemannProjectivity.BoundedPolynomial
import OAI.Geometry.ComplexTorus.RiemannProjectivity.RootContinuityAt
import OAI.Geometry.ComplexTorus.RiemannProjectivity.MonicRoot
import OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.SquarefreeFamilies

/-! # Local Reduced -/

namespace OAI.Geometry.ComplexTorus.RiemannProjectivity.LocalReduced.Constructions.LocalReducedFamily

noncomputable section

/-!
# RiemannProjectivity: holomorphic reduction of a monic polynomial family

After removing repeated roots generically, bounded coefficients extend
across the exceptional set. Root continuity in both families proves that
the extension preserves the root set at every base point.
-/

open Set Filter _root_.Polynomial
open scoped _root_.Topology BigOperators

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]

omit [FiniteDimensional ℂ V] in
theorem exists_root_bound {P : V → ℂ[X]} {O : Set V} (hO : IsOpen O)
    (hcoeff : ∀ j, DifferentiableOn ℂ (fun y => (P y).coeff j) O)
    (k : ℕ) (hP : ∀ y, (P y).Monic ∧ (P y).natDegree = k) {x : V} (hx : x ∈ O) :
    ∃ (U : Set V) (C : ℝ), IsOpen U ∧ x ∈ U ∧ U ⊆ O ∧
      ∀ y ∈ U, ∀ z, (P y).eval z = 0 → ‖z‖ ≤ C := by
  let B : V → ℝ := fun y => (∑ j ∈ Finset.range k, ‖(P y).coeff j‖) + 1
  have hB : ContinuousOn B O :=
    (continuousOn_finsetSum _ (fun j _ => (hcoeff j).continuousOn.norm)).add continuousOn_const
  let U := O ∩ B ⁻¹' Set.Iio (B x + 1)
  refine ⟨U, B x + 1, hB.isOpen_inter_preimage hO isOpen_Iio,
    ⟨hx, show B x < B x + 1 from lt_add_one _⟩, inter_subset_left, ?_⟩
  intro y hy z hz
  exact (MonicRoot.Constructions.MonicRootBound.norm_root_le_sum_coeff (hP y).1 (hP y).2.le hz).trans hy.2.le

theorem exists_reduced_family {P : V → ℂ[X]} {O : Set V} (hO : IsOpen O)
    (hcoeff : ∀ j, DifferentiableOn ℂ (fun y => (P y).coeff j) O)
    (k : ℕ) (hP : ∀ y, (P y).Monic ∧ (P y).natDegree = k) {x : V} (hx : x ∈ O) :
    ∃ (m : ℕ) (Q : V → ℂ[X]) (U : Set V) (c : V → ℂ),
      IsOpen U ∧ x ∈ U ∧ U ⊆ O ∧ DifferentiableOn ℂ c U ∧
      U ⊆ closure {y | y ∈ U ∧ c y ≠ 0} ∧
      (∀ j, DifferentiableOn ℂ (fun y => (Q y).coeff j) U) ∧
      (∀ y, (Q y).Monic ∧ (Q y).natDegree = m) ∧
      (∀ y ∈ U, c y ≠ 0 → (Q y).Separable) ∧
      ∀ y ∈ U, ∀ z, (P y).eval z = 0 ↔ (Q y).eval z = 0 := by
  obtain ⟨A, C, hA, hxA, hAO, hbound⟩ := exists_root_bound hO hcoeff k hP hx
  obtain ⟨m, G, c, B, hB, hxB, hBA, hc, hcn, hGcoeff, hG⟩ :=
    AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.SquarefreeFamilies.Constructions.GenericPolynomial.exists_monic_separable_common_root_family
      (fun _ : Unit => P) hA hxA k (fun _ j => (hcoeff j).mono hAO)
      (fun _ y _ => (hP y).2.le) (fun y _ => ⟨(), (hP y).1.ne_zero⟩)
  have hBG (y : V) (hy : y ∈ B) (hcy : c y ≠ 0) (z : ℂ) (hz : (G y).eval z = 0) : ‖z‖ ≤ C :=
    hbound y (hBA hy) z (((hG y hy hcy).2.2.2 z).mpr hz ())
  obtain ⟨Q, W, hW, hxW, hWB, hQcoeff, hQ, hQG⟩ :=
    BoundedPolynomial.Constructions.BoundedPolynomialExtension.exists_extension hB hc hxB hcn m hGcoeff
      (fun y hy hcy => ⟨(hG y hy hcy).1, (hG y hy hcy).2.1⟩) hBG
  obtain ⟨U, hU, hxU, hUW, hdense⟩ :=
    AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.GenericDegree.Constructions.GenericPolynomial.exists_dense_nonzero_neighborhood hW hxW (hc.mono hWB) hcn
  have hUO : U ⊆ O := hUW.trans (hWB.trans (hBA.trans hAO))
  have hgeneric (y : V) (hy : y ∈ U) (hcy : c y ≠ 0) (z : ℂ) :
      (P y).eval z = 0 ↔ (Q y).eval z = 0 := by
    rw [hQG y (hUW hy) hcy]
    simpa only [forall_const] using (hG y (hWB (hUW hy)) hcy).2.2.2 z
  refine ⟨m, Q, U, c, hU, hxU, hUO, (hc.mono hWB).mono hUW, hdense,
    fun j => (hQcoeff j).mono hUW, hQ, ?_, ?_⟩
  · intro y hy hcy
    rw [hQG y (hUW hy) hcy]
    exact (hG y (hWB (hUW hy)) hcy).2.2.1
  · intro y hy z
    have hPc := fun j => ((hcoeff j).differentiableAt (hO.mem_nhds (hUO hy))).continuousAt
    have hQc := fun j => ((hQcoeff j).differentiableAt (hW.mem_nhds (hUW hy))).continuousAt
    exact ⟨RootContinuityAt.Constructions.RootClosure.root_imp_of_generic k m hP (fun y => (hQ y).2.le) (hdense hy) hPc hQc
      (fun y hy z => (hgeneric y hy.1 hy.2 z).mp),
      RootContinuityAt.Constructions.RootClosure.root_imp_of_generic m k hQ (fun y => (hP y).2.le) (hdense hy) hQc hPc
        (fun y hy z => (hgeneric y hy.1 hy.2 z).mpr)⟩

end

end OAI.Geometry.ComplexTorus.RiemannProjectivity.LocalReduced.Constructions.LocalReducedFamily
