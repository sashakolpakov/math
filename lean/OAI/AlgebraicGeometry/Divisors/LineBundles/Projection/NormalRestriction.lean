import OAI.AlgebraicGeometry.Divisors.LineBundles.Projection.NormalClass
import OAI.AlgebraicGeometry.CycleClass.Thom.ThomOpenRestriction

/-! # Normal Restriction -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Projection.NormalRestriction.BundleCycles

noncomputable section

/-! Restricting a projection pullback to the constructed product normal
neighborhood commutes with the actual restriction on the base. -/

open _root_.CategoryTheory

def normalProductProjection (B N : Type) [TopologicalSpace B] [TopologicalSpace N] :
    TopCat.of (B × N) ⟶ TopCat.of N := TopCat.ofHom ⟨Prod.snd, continuous_snd⟩

theorem normalProductProjection_mapsTo {B M N : Type} [TopologicalSpace B] [TopologicalSpace N]
    (u : M → N) : Set.MapsTo (normalProductProjection B N)
      (Set.range (Prod.map (id : B → B) u))ᶜ (Set.range u)ᶜ := by
  rintro z hz ⟨m, hm⟩
  exact hz ⟨(z.1, m), Prod.ext rfl hm⟩

variable {M N B E F : Type} [TopologicalSpace N] [TopologicalSpace B]
    [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [NormedSpace ℝ F]
    {u : M → N} {x : M} {p : ℕ}
    (P : ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair E (Fin p → ℂ) u x)
    (c : OpenPartialHomeomorph B F) (b : B) (hb : b ∈ c.source) (hc : c b = 0)

omit [NormedSpace ℝ E] [NormedSpace ℝ F] in
theorem projectionNormalPair_restriction
    (a : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of N) (Set.range u)ᶜ (2 * p)) :
    CycleClass.Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) (TopCat.of (B × N))
      (Set.range (Prod.map (id : B → B) u))ᶜ (NormalPair.BundleCycles.projectionNormalPair P c b hb hc).openNeighborhood (2 * p)
      (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (normalProductProjection B N)
        (normalProductProjection_mapsTo u) (2 * p) a) =
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (NormalClass.BundleCycles.projectionNormalPairToBase P c b hb hc)
      (NormalClass.BundleCycles.projectionNormalPairToBase_mapsTo P c b hb hc) (2 * p)
      (CycleClass.Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) (TopCat.of N) (Set.range u)ᶜ
        P.openNeighborhood (2 * p) a) := by
  let Q := NormalPair.BundleCycles.projectionNormalPair P c b hb hc
  let g := NormalClass.BundleCycles.projectionNormalPairToBase P c b hb hc
  let i := CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of (B × N)) Q.neighborhood
  let j := CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of N) P.neighborhood
  have hi : Set.MapsTo i Q.relativeComplement (Set.range (Prod.map (id : B → B) u))ᶜ :=
    fun _ hy => hy
  have hj : Set.MapsTo j P.relativeComplement (Set.range u)ᶜ := fun _ hy => hy
  have he : i ≫ normalProductProjection B N = g ≫ j := by
    ext z
    rfl
  have h₁ := ConcreteCategory.congr_hom
    (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCohomologyMap_comp (ModuleCat.of ℚ ℚ) i (normalProductProjection B N)
      hi (normalProductProjection_mapsTo u) (2 * p)) a
  have h₂ := ConcreteCategory.congr_hom
    (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCohomologyMap_comp (ModuleCat.of ℚ ℚ) g j
      (NormalClass.BundleCycles.projectionNormalPairToBase_mapsTo P c b hb hc) hj (2 * p)) a
  have h₃ := ConcreteCategory.congr_hom
    (CycleClass.Thom.ThomOpenRestriction.Constructions.pairMap_congr he
      ((normalProductProjection_mapsTo u).comp hi)
      (hj.comp (NormalClass.BundleCycles.projectionNormalPairToBase_mapsTo P c b hb hc)) (2 * p)) a
  exact h₁.trans (h₃.trans h₂.symm)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Projection.NormalRestriction.BundleCycles
