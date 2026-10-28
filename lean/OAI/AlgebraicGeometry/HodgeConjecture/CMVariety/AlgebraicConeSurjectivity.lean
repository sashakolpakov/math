import OAI.AlgebraicGeometry.HodgeConjecture.CMVariety.AlgebraicCone
import OAI.AlgebraicGeometry.HodgeConjecture.CMVariety.AlgebraicFiniteConeFibers
import OAI.Geometry.ComplexTorus.RiemannProjectivity.AnalyticCone
import OAI.Geometry.ComplexTorus.RiemannProjectivity.AnalyticIrreducibilityEq
import OAI.AlgebraicGeometry.HodgeConjecture.CMVariety.AlgebraicRegularCone
import Mathlib.Analysis.Normed.Module.Connected

/-! # Algebraic Cone Surjectivity -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMVariety.AlgebraicConeSurjectivity.CM.Abelian.Algebraization.ConeSurjectivity

noncomputable section

open Set Filter _root_.Module
open scoped _root_.Topology

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℂ W]

omit [FiniteDimensional ℂ W] in
theorem local_equations_of_holomorphic {S : Set W} {x : W}
    (h : ComplexGroups.HolomorphicAlgebraicity.ZeroLocus.Constructions.Cone.HolomorphicZeroSetAt S x) : Geometry.ComplexTorus.RiemannProjectivity.AnalyticIrreducibilityEq.Constructions.AnalyticIrreducibility.HasLocalEquations S x := by
  obtain ⟨U, hU, hx, m, f, hf, heq⟩ := h
  refine ⟨U, hU, hx, range f, ?_, ?_⟩
  · rintro _ ⟨i, rfl⟩
    exact hf i
  · intro y hy
    rw [heq y hy]
    exact ⟨fun h _ ⟨i, hi⟩ => hi ▸ h i, fun h i => h _ ⟨i, rfl⟩⟩

theorem eq_univ_of_interior_of_analytic_off_zero [Nontrivial W] {S : Set W}
    (hS : IsClosed S) (hlocal : ∀ x ∈ S, x ≠ 0 → ComplexGroups.HolomorphicAlgebraicity.ZeroLocus.Constructions.Cone.HolomorphicZeroSetAt S x)
    (hne : (interior S).Nonempty) : S = univ := by
  let : FiniteDimensional ℝ W := FiniteDimensional.trans ℝ ℂ W
  have hdim : 1 < Module.rank ℝ W := by
    rw [← Module.finrank_eq_rank]
    have he : finrank ℝ W = 2 * finrank ℂ W := by
      rw [← Module.finrank_mul_finrank ℝ ℂ W, Complex.finrank_real_complex]
    have hp := finrank_pos (R := ℂ) (M := W)
    have hn : 1 < finrank ℝ W := by omega
    exact_mod_cast hn
  let U := ({0} : Set W)ᶜ
  let : PreconnectedSpace U := isPreconnected_iff_preconnectedSpace.mp
    (isConnected_compl_singleton_of_one_lt_rank hdim (0 : W)).isPreconnected
  have heq : (Subtype.val ⁻¹' interior S : Set U) = Subtype.val ⁻¹' closure (interior S) := by
    ext x
    constructor
    · exact fun h => subset_closure h
    · intro h
      have hxS := hS.closure_subset (closure_mono interior_subset h)
      exact Geometry.ComplexTorus.RiemannProjectivity.AnalyticIrreducibilityEq.Constructions.AnalyticIrreducibility.mem_interior_of_local_equations
        (local_equations_of_holomorphic (hlocal x hxS x.property)) h
  have hcl : IsClopen (Subtype.val ⁻¹' interior S : Set U) := by
    refine ⟨?_, isOpen_interior.preimage continuous_subtype_val⟩
    rw [heq]
    exact isClosed_closure.preimage continuous_subtype_val
  have hneU : (interior S ∩ U).Nonempty :=
    dense_iff_inter_open.mp (dense_compl_singleton (0 : W)) _ isOpen_interior hne
  rcases isClopen_iff.mp hcl with hempty | hfull
  · obtain ⟨x, hx, hxU⟩ := hneU
    have hmem : (⟨x, hxU⟩ : U) ∈ Subtype.val ⁻¹' interior S := hx
    simp only [hempty, mem_empty_iff_false] at hmem
  · have hUS : U ⊆ S := by
      intro x hx
      have hmem : (⟨x, hx⟩ : U) ∈ Subtype.val ⁻¹' interior S := by rw [hfull]; trivial
      exact interior_subset hmem
    apply eq_univ_of_forall
    intro x
    exact hS.closure_subset (closure_mono hUS (dense_compl_singleton (0 : W) x))

omit [FiniteDimensional ℂ W] in
theorem surjective_of_image_interior {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℂ V] (L : V →L[ℂ] W) {S : Set V}
    (hne : (interior (L '' S)).Nonempty) : Function.Surjective L := by
  apply LinearMap.range_eq_top.mp
  apply L.range.eq_top_of_nonempty_interior'
  have hsub : L '' S ⊆ (L.range : Set W) := by
    rintro _ ⟨v, _, hv⟩
    exact ⟨v, hv⟩
  exact hne.mono (interior_mono hsub)

theorem surjective_cone_projection {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V] [Nontrivial W]
    (L : V →L[ℂ] W) {S : Set V} (hS : IsClosed S)
    (hcone : ∀ (c : ℂ) ⦃v : V⦄, v ∈ S → c • v ∈ S)
    (hkernel : ∀ v ∈ S, L v = 0 → v = 0)
    (hlocal : ∀ v ∈ S, v ≠ 0 → ComplexGroups.HolomorphicAlgebraicity.ZeroLocus.Constructions.Cone.HolomorphicZeroSetAt S v)
    (hne : (interior (L '' S)).Nonempty) : Function.Surjective (fun v : S => L v) := by
  have hproper := ComplexGroups.HolomorphicAlgebraicity.Projection.Constructions.Cone.isProperMap_projection hS hcone L hkernel
  have hrange : range (fun v : S => L v) = L '' S := by
    ext y
    exact ⟨fun ⟨v, hv⟩ => ⟨v, v.property, hv⟩,
      fun ⟨v, hv, he⟩ => ⟨⟨v, hv⟩, he⟩⟩
  have hclosed : IsClosed (L '' S) := by
    rw [← hrange]
    exact hproper.isClosedMap.isClosed_range
  have hfull := eq_univ_of_interior_of_analytic_off_zero hclosed
    (Geometry.ComplexTorus.RiemannProjectivity.AnalyticCone.Constructions.AnalyticConeImage.linear_projection L (surjective_of_image_interior L hne)
      hS hcone hkernel hlocal) hne
  exact range_eq_univ.mp (hrange.trans hfull)

/-- The actual CM cone admits a finite, surjective, proper linear projection
to affine space of complex dimension `dim(T) + 1`. -/
theorem period_cone_finite_surjective
    (Φ : ProjectiveTorusData.CM.Abelian.ProjectivePeriodData) :
    ∃ (n : ℕ) (f : Φ.periodTorus → Projectivization ℂ (Fin (n + 1) → ℂ))
      (L : (Fin (n + 1) → ℂ) →L[ℂ]
        (Fin (Module.finrank ℂ (Φ.space) + 1) → ℂ)),
      Topology.IsClosedEmbedding f ∧
      IsProperMap (fun v : ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.projectiveCone (range f) => L v) ∧
      Function.Surjective (fun v : ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.projectiveCone (range f) => L v) ∧
      (∀ y, {v : Fin (n + 1) → ℂ | v ∈ ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.projectiveCone (range f) ∧ L v = y}.Finite) ∧
      ∃ C : ℝ, 0 < C ∧ ∀ v ∈ ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.projectiveCone (range f), ‖v‖ ≤ C * ‖L v‖ := by
  obtain ⟨n, f, L, hf, hd, hL, hp, hi⟩ :=
    AlgebraicRegularCone.CM.Abelian.Algebraization.RegularCone.proper_period_cone_projection_with_interior_and_immersions Φ
  have hclosed := ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.isClosed_projectiveCone (range f) hf.isClosed_range
  have hlocal := AlgebraicFiniteConeFibers.CM.Abelian.Algebraization.FiniteConeFibers.cone_holomorphic_of_period_embedding Φ f hf hd
  exact ⟨n, f, L, hf, hp,
    surjective_cone_projection L hclosed (ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.smul_mem_projectiveCone _) hL hlocal hi,
    AlgebraicFiniteConeFibers.CM.Abelian.Algebraization.FiniteConeFibers.finite_proper_cone_fiber L hp hL hlocal,
    ComplexGroups.HolomorphicAlgebraicity.Projection.Constructions.Cone.norm_le_projection hclosed (ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.smul_mem_projectiveCone _) L hL⟩

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMVariety.AlgebraicConeSurjectivity.CM.Abelian.Algebraization.ConeSurjectivity
