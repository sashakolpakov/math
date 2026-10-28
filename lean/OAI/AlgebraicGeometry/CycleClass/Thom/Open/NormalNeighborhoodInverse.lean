import OAI.AlgebraicGeometry.CycleClass.Thom.NormalPair.AmbientTransport

/-! # Normal Neighborhood Inverse -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.CycleClass.Thom.Open.NormalNeighborhoodInverse.Constructions.PairTransport

/-! Actual full-image normal pairs and normalized classes transported
along an open embedding of ambient spaces. -/

open _root_.CategoryTheory _root_.TopologicalSpace
open scoped _root_.Topology

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {M N N' E F : Type} [TopologicalSpace N] [TopologicalSpace N']
  [NormedAddCommGroup E] [NormedAddCommGroup F]
  {f : M → N} {x : M} (P : ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair E F f x)
  (e : N → N') (he : Topology.IsOpenEmbedding e)

def openTransportNormalPair : ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair E F (e ∘ f) x where
  radius := P.radius
  radius_pos := P.radius_pos
  ambientChart := P.ambientChart.lift_openEmbedding he
  product_subset_target := P.product_subset_target
  point_mem_source := ⟨f x, P.point_mem_source, rfl⟩
  point_coordinates := by
    rw [Function.comp_apply, OpenPartialHomeomorph.lift_openEmbedding_apply]
    exact P.point_coordinates
  range_iff := by
    intro y hy
    obtain ⟨w, hw, rfl⟩ := hy
    simp only [OpenPartialHomeomorph.lift_openEmbedding_symm, Function.comp_apply,
      OpenPartialHomeomorph.lift_openEmbedding_apply]
    rw [← P.range_iff (P.ambientChart.symm w) ⟨w, hw, rfl⟩]
    constructor
    · rintro ⟨a, ha⟩
      exact ⟨a, he.injective ha⟩
    · rintro ⟨a, ha⟩
      exact ⟨a, congrArg e ha⟩

theorem openTransportNormalPair_neighborhood :
    (openTransportNormalPair P e he).neighborhood = e '' P.neighborhood := by
  simp only [ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair.neighborhood, openTransportNormalPair,
    OpenPartialHomeomorph.lift_openEmbedding_symm, Set.image_comp]

def openTransportNormalNeighborhoodMap : TopCat.of P.neighborhood ⟶
    TopCat.of (openTransportNormalPair P e he).neighborhood := by
  let g : P.neighborhood → (openTransportNormalPair P e he).neighborhood := fun z =>
    ⟨e z.val, (Set.ext_iff.mp (openTransportNormalPair_neighborhood P e he) (e z.val)).mpr
      ⟨z.val, z.property, rfl⟩⟩
  refine TopCat.ofHom ⟨g, ?_⟩
  apply Continuous.subtype_mk
  exact he.continuous.comp continuous_subtype_val

theorem openTransportNormalNeighborhoodMap_normalCoordinate :
    openTransportNormalNeighborhoodMap P e he ≫ (openTransportNormalPair P e he).normalCoordinate =
      P.normalCoordinate := by
  ext z
  change ((P.ambientChart.lift_openEmbedding he) (e z.val)).2 = (P.ambientChart z.val).2
  rw [OpenPartialHomeomorph.lift_openEmbedding_apply]

theorem openTransportNormalNeighborhoodMap_mapsTo :
    Set.MapsTo (openTransportNormalNeighborhoodMap P e he) P.relativeComplement
      (openTransportNormalPair P e he).relativeComplement := by
  intro z hz h
  obtain ⟨a, ha⟩ := h
  exact hz ⟨a, he.injective ha⟩

theorem openTransportNormalClass [NormedSpace ℝ E] {p : ℕ}
    (Q : ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair E (Fin p → ℂ) f x) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (openTransportNormalNeighborhoodMap Q e he)
      (openTransportNormalNeighborhoodMap_mapsTo Q e he) (2 * p)
      (openTransportNormalPair Q e he).rationalClassFin = Q.rationalClassFin := by
  rw [Q.rationalClassFin_eq_normalPullback, (openTransportNormalPair Q e he).rationalClassFin_eq_normalPullback]
  simp only [ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair.normalCohomologyMap]
  have h := ConcreteCategory.congr_hom
    (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCohomologyMap_comp (ModuleCat.of ℚ ℚ)
      (openTransportNormalNeighborhoodMap Q e he) (openTransportNormalPair Q e he).normalCoordinate
      (openTransportNormalNeighborhoodMap_mapsTo Q e he)
      (openTransportNormalPair Q e he).normalCoordinate_mapsTo (2 * p))
    (Geometric.RationalLocalPurity.Cycles.complexNormalRationalDualClass p)
  simp only [openTransportNormalNeighborhoodMap_normalCoordinate, ConcreteCategory.comp_apply] at h
  exact h

end AlgebraicGeometry.CycleClass.Thom.Open.NormalNeighborhoodInverse.Constructions.PairTransport

namespace AlgebraicGeometry.CycleClass.Thom.Open.NormalNeighborhoodInverse.Constructions

/-! The lifted normal neighborhood of an actual ambient open subset
has a literal inverse map to the original neighborhood. Both maps
preserve the genuine normal coordinates and supported normal classes. -/

open _root_.CategoryTheory _root_.TopologicalSpace

open OAI.AlgebraicGeometry.CycleClass.Thom.Open.NormalNeighborhoodInverse.Constructions.PairTransport

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {M N E F : Type} [TopologicalSpace N] [NormedAddCommGroup E] [NormedAddCommGroup F]
  (U : Opens N) {f : M → U} {x : M} (P : ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair E F f x)

theorem liftedPoint_mem_open (y : (PairTransport.openTransportNormalPair P Subtype.val U.isOpenEmbedding').neighborhood) :
    y.val ∈ U := by
  have hy := (Set.ext_iff.mp
    (PairTransport.openTransportNormalPair_neighborhood P Subtype.val U.isOpenEmbedding') y.val).mp y.property
  obtain ⟨w, _, hw⟩ := hy
  exact hw ▸ w.property

theorem liftedPoint_mem_pair (y : (PairTransport.openTransportNormalPair P Subtype.val U.isOpenEmbedding').neighborhood) :
    (⟨y.val, liftedPoint_mem_open U P y⟩ : U) ∈ P.neighborhood := by
  have hy := (Set.ext_iff.mp
    (PairTransport.openTransportNormalPair_neighborhood P Subtype.val U.isOpenEmbedding') y.val).mp y.property
  obtain ⟨w, hw, he⟩ := hy
  have h : (⟨y.val, liftedPoint_mem_open U P y⟩ : U) = w := Subtype.ext he.symm
  rw [h]
  exact hw

def liftedNormalInverse :
    TopCat.of (PairTransport.openTransportNormalPair P Subtype.val U.isOpenEmbedding').neighborhood ⟶
      TopCat.of P.neighborhood :=
  TopCat.ofHom ⟨fun y => ⟨⟨y.val, liftedPoint_mem_open U P y⟩, liftedPoint_mem_pair U P y⟩,
    (continuous_subtype_val.subtype_mk _).subtype_mk _⟩

theorem inverse_forward :
    liftedNormalInverse U P ≫ PairTransport.openTransportNormalNeighborhoodMap P Subtype.val U.isOpenEmbedding' = 𝟙 _ := by
  ext y
  rfl

theorem forward_inverse :
    PairTransport.openTransportNormalNeighborhoodMap P Subtype.val U.isOpenEmbedding' ≫ liftedNormalInverse U P = 𝟙 _ := by
  ext y
  rfl

theorem inverse_normalCoordinate :
    liftedNormalInverse U P ≫ P.normalCoordinate =
      (PairTransport.openTransportNormalPair P Subtype.val U.isOpenEmbedding').normalCoordinate := by
  rw [← PairTransport.openTransportNormalNeighborhoodMap_normalCoordinate P Subtype.val U.isOpenEmbedding',
    ← Category.assoc, inverse_forward, Category.id_comp]

theorem inverse_mapsTo : Set.MapsTo (liftedNormalInverse U P)
    (PairTransport.openTransportNormalPair P Subtype.val U.isOpenEmbedding').relativeComplement P.relativeComplement := by
  intro y hy h
  obtain ⟨t, ht⟩ := h
  exact hy ⟨t, congrArg Subtype.val ht⟩

theorem inverse_normalClass [NormedSpace ℝ E] {p : ℕ}
    (Q : ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair E (Fin p → ℂ) f x) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (liftedNormalInverse U Q)
      (inverse_mapsTo U Q) (2 * p) Q.rationalClassFin =
      (PairTransport.openTransportNormalPair Q Subtype.val U.isOpenEmbedding').rationalClassFin := by
  rw [Q.rationalClassFin_eq_normalPullback,
    (PairTransport.openTransportNormalPair Q Subtype.val U.isOpenEmbedding').rationalClassFin_eq_normalPullback]
  have hc := ConcreteCategory.congr_hom
    (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCohomologyMap_comp (ModuleCat.of ℚ ℚ) (liftedNormalInverse U Q) Q.normalCoordinate
      (inverse_mapsTo U Q) Q.normalCoordinate_mapsTo (2 * p)) (Geometric.RationalLocalPurity.Cycles.complexNormalRationalDualClass p)
  simpa only [inverse_normalCoordinate, ConcreteCategory.comp_apply,
    ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair.normalCohomologyMap] using hc

end AlgebraicGeometry.CycleClass.Thom.Open.NormalNeighborhoodInverse.Constructions

end

end OAI
