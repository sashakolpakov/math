import OAI.AlgebraicGeometry.CycleClass.Geometric.ImmersionNormalFin

/-! # Ambient Transport -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.NormalPair.AmbientTransport.Constructions

noncomputable section

/-! Transport of actual full-image normal pairs along an ambient
homeomorphism, with unchanged normal coordinates and normalized classes. -/

open _root_.CategoryTheory _root_.TopologicalSpace OAI.AlgebraicGeometry.CycleClass.Geometric.ImmersionNormalFin.Cycles
open scoped _root_.Topology

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {M N N' E F : Type} [TopologicalSpace N] [TopologicalSpace N']
  [NormedAddCommGroup E] [NormedAddCommGroup F]
  {f : M → N} {x : M} (P : ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair E F f x) (e : N ≃ₜ N')

def transportNormalPair : ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair E F (e ∘ f) x where
  radius := P.radius
  radius_pos := P.radius_pos
  ambientChart := (P.ambientChart.symm.transHomeomorph e).symm
  product_subset_target := P.product_subset_target
  point_mem_source := by
    change e.symm (e (f x)) ∈ P.ambientChart.source
    rw [e.symm_apply_apply]
    exact P.point_mem_source
  point_coordinates := by
    change P.ambientChart (e.symm (e (f x))) = (0, 0)
    rw [e.symm_apply_apply]
    exact P.point_coordinates
  range_iff := by
    intro y hy
    have hn : e.symm y ∈ P.neighborhood := by
      obtain ⟨w, hw, rfl⟩ := hy
      exact ⟨w, hw, (e.symm_apply_apply (P.ambientChart.symm w)).symm⟩
    change y ∈ Set.range (e ∘ f) ↔ (P.ambientChart (e.symm y)).2 = 0
    rw [← P.range_iff (e.symm y) hn]
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨a, (e.symm_apply_apply (f a)).symm⟩
    · rintro ⟨a, ha⟩
      exact ⟨a, (congrArg e ha).trans (e.apply_symm_apply y)⟩

theorem transportNormalPair_neighborhood :
    (transportNormalPair P e).neighborhood = e '' P.neighborhood := by
  change (e ∘ P.ambientChart.symm) '' _ = e '' (P.ambientChart.symm '' _)
  exact Set.image_comp _ _ _

def transportNormalNeighborhoodMap : TopCat.of P.neighborhood ⟶
    TopCat.of (transportNormalPair P e).neighborhood := by
  let g : P.neighborhood → (transportNormalPair P e).neighborhood := fun z =>
    ⟨e z.val, (Set.ext_iff.mp (transportNormalPair_neighborhood P e) (e z.val)).mpr
      ⟨z.val, z.property, rfl⟩⟩
  refine TopCat.ofHom ⟨g, ?_⟩
  apply Continuous.subtype_mk
  exact e.continuous.comp continuous_subtype_val

theorem transportNormalNeighborhoodMap_normalCoordinate :
    transportNormalNeighborhoodMap P e ≫ (transportNormalPair P e).normalCoordinate = P.normalCoordinate := by
  ext z
  change (P.ambientChart (e.symm (e z.val))).2 = (P.ambientChart z.val).2
  rw [e.symm_apply_apply]

theorem transportNormalNeighborhoodMap_mapsTo :
    Set.MapsTo (transportNormalNeighborhoodMap P e) P.relativeComplement
      (transportNormalPair P e).relativeComplement := by
  intro z hz h
  obtain ⟨a, ha⟩ := h
  exact hz ⟨a, e.injective ha⟩

theorem transportNormalClass [NormedSpace ℝ E] {p : ℕ}
    (Q : ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair E (Fin p → ℂ) f x) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (transportNormalNeighborhoodMap Q e)
      (transportNormalNeighborhoodMap_mapsTo Q e) (2 * p)
      (transportNormalPair Q e).rationalClassFin = Q.rationalClassFin := by
  rw [Q.rationalClassFin_eq_normalPullback, (transportNormalPair Q e).rationalClassFin_eq_normalPullback]
  simp only [ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair.normalCohomologyMap]
  have h := ConcreteCategory.congr_hom
    (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCohomologyMap_comp (ModuleCat.of ℚ ℚ)
      (transportNormalNeighborhoodMap Q e) (transportNormalPair Q e).normalCoordinate
      (transportNormalNeighborhoodMap_mapsTo Q e) (transportNormalPair Q e).normalCoordinate_mapsTo (2 * p))
    (Geometric.RationalLocalPurity.Cycles.complexNormalRationalDualClass p)
  simp only [transportNormalNeighborhoodMap_normalCoordinate, ConcreteCategory.comp_apply] at h
  exact h

end

end OAI.AlgebraicGeometry.CycleClass.Thom.NormalPair.AmbientTransport.Constructions
