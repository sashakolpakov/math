import OAI.AlgebraicGeometry.Divisors.LineBundles.Projection.NormalPair
import OAI.AlgebraicGeometry.Divisors.LineBundles.Normal.PairPullbackClass
import OAI.AlgebraicGeometry.CycleClass.Thom.Product.NormalDifferentiable

/-! # Normal Class -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Projection.NormalClass.BundleCycles

noncomputable section

/-! The constructed projection normal chart is differentiable in both
directions and its normalized class is the actual projection pullback. -/

open _root_.CategoryTheory
open OAI.AlgebraicGeometry.CycleClass.Thom.Product.NormalDifferentiable.Constructions
open scoped _root_.Manifold

variable {M N B E F : Type} [TopologicalSpace N] [TopologicalSpace B]
    [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [NormedSpace ℝ F]
    {u : M → N} {x : M} {p : ℕ}
    (P : ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair E (Fin p → ℂ) u x)
    (c : OpenPartialHomeomorph B F) (b : B) (hb : b ∈ c.source) (hc : c b = 0)

def projectionNormalPairToBase : TopCat.of (NormalPair.BundleCycles.projectionNormalPair P c b hb hc).neighborhood ⟶
    TopCat.of P.neighborhood := TopCat.ofHom {
  toFun := fun z => ⟨z.val.2, (NormalPair.BundleCycles.projectionNormalPair_neighborhood P c b hb hc z.property).2⟩
  continuous_toFun := (continuous_snd.comp continuous_subtype_val).subtype_mk _ }

omit [NormedSpace ℝ E] [NormedSpace ℝ F] in
theorem projectionNormalPairToBase_mapsTo :
    Set.MapsTo (projectionNormalPairToBase P c b hb hc)
      (NormalPair.BundleCycles.projectionNormalPair P c b hb hc).relativeComplement P.relativeComplement := by
  intro z hz h
  apply hz
  obtain ⟨m, hm⟩ := h
  exact ⟨(z.val.1, m), Prod.ext rfl hm⟩

omit [NormedSpace ℝ E] [NormedSpace ℝ F] in
theorem projectionNormalPairToBase_coordinate :
    projectionNormalPairToBase P c b hb hc ≫ P.normalCoordinate =
      (NormalPair.BundleCycles.projectionNormalPair P c b hb hc).normalCoordinate := by
  ext z
  rfl

theorem projectionNormalPair_class :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (projectionNormalPairToBase P c b hb hc)
      (projectionNormalPairToBase_mapsTo P c b hb hc) (2 * p) P.rationalClassFin =
      (NormalPair.BundleCycles.projectionNormalPair P c b hb hc).rationalClassFin :=
  Normal.PairPullbackClass.BundleCycles.normalPairClass_pullback P (NormalPair.BundleCycles.projectionNormalPair P c b hb hc)
    (projectionNormalPairToBase P c b hb hc) (projectionNormalPairToBase_mapsTo P c b hb hc)
    (projectionNormalPairToBase_coordinate P c b hb hc)

omit [NormedSpace ℝ E] [NormedSpace ℝ F] in
theorem projectionNormalPair_mdifferentiable {G H : Type}
    [NormedAddCommGroup G] [NormedSpace ℂ G] [ChartedSpace G B]
    [NormedAddCommGroup H] [NormedSpace ℂ H] [ChartedSpace H N]
    (hc' : c.MDifferentiable 𝓘(ℂ, G) 𝓘(ℂ, F))
    (hP : P.ambientChart.MDifferentiable 𝓘(ℂ, H) 𝓘(ℂ, E × (Fin p → ℂ))) :
    (NormalPair.BundleCycles.projectionNormalPair P c b hb hc).ambientChart.MDifferentiable
      (𝓘(ℂ, G).prod 𝓘(ℂ, H)) 𝓘(ℂ, (F × E) × (Fin p → ℂ)) := by
  change (NormalPair.BundleCycles.projectionNormalChart P c).MDifferentiable _ _
  unfold NormalPair.BundleCycles.projectionNormalChart
  rw [OpenPartialHomeomorph.transHomeomorph_eq_trans]
  exact (CycleClass.Thom.Product.NormalDifferentiable.Constructions.productChart_mdifferentiable c P.ambientChart hc' hP).trans
    (CycleClass.Thom.Product.NormalDifferentiable.Constructions.linearCoordinates_mdifferentiable (NormalPair.BundleCycles.projectionNormalCoordinates (E := E) (F := F) (p := p)))

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Projection.NormalClass.BundleCycles
