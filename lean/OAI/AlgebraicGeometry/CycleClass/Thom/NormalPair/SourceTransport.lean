import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.NormalPairReindex
import OAI.AlgebraicGeometry.CycleClass.Geometric.ImmersionNormalFin

/-! # Source Transport -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.NormalPair.SourceTransport.Constructions

noncomputable section

/-! Reparametrizing a full support by a surjective source map preserves
its actual normal chart and normalized local relative class. -/

open _root_.CategoryTheory OAI.AlgebraicGeometry.CycleClass.Geometric.ImmersionNormalFin.Cycles

open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.NormalPairReindex.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {M M' N E F : Type} [TopologicalSpace N]
  [NormedAddCommGroup E] [NormedAddCommGroup F]
  {f : M → N} (a : M' → M) (ha : Function.Surjective a) (x : M')
  (P : ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair E F f (a x))

omit [TopologicalSpace N] in
theorem sourceTransport_range (ha : Function.Surjective a) : Set.range (f ∘ a) = Set.range f := by
  rw [Set.range_comp, ha.range_eq, Set.image_univ]

def sourceTransportNormalPair : ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair E F (f ∘ a) x :=
  HodgeConjecture.DegreeTwo.NormalPairReindex.Constructions.normalPairReplaceSupport P (f ∘ a) x rfl (fun y _ => by rw [sourceTransport_range a ha])

def sourceTransportNeighborhoodMap :
    TopCat.of (sourceTransportNormalPair a ha x P).neighborhood ⟶ TopCat.of P.neighborhood := 𝟙 _

theorem sourceTransportNeighborhoodMap_mapsTo :
    Set.MapsTo (sourceTransportNeighborhoodMap a ha x P)
      (sourceTransportNormalPair a ha x P).relativeComplement P.relativeComplement := by
  intro z hz
  change z.val ∉ Set.range (f ∘ a) at hz
  change z.val ∉ Set.range f
  rwa [sourceTransport_range a ha] at hz

theorem sourceTransportNeighborhoodMap_normalCoordinate :
    sourceTransportNeighborhoodMap a ha x P ≫ P.normalCoordinate =
      (sourceTransportNormalPair a ha x P).normalCoordinate := Category.id_comp _

variable [NormedSpace ℝ E]

theorem sourceTransportNormalClass {p : ℕ} (Q : ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair E (Fin p → ℂ) f (a x)) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (sourceTransportNeighborhoodMap a ha x Q)
      (sourceTransportNeighborhoodMap_mapsTo a ha x Q) (2 * p) Q.rationalClassFin =
        (sourceTransportNormalPair a ha x Q).rationalClassFin := by
  rw [Q.rationalClassFin_eq_normalPullback, (sourceTransportNormalPair a ha x Q).rationalClassFin_eq_normalPullback]
  simp only [ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair.normalCohomologyMap]
  have h := ConcreteCategory.congr_hom
    (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCohomologyMap_comp (ModuleCat.of ℚ ℚ)
      (sourceTransportNeighborhoodMap a ha x Q) Q.normalCoordinate
      (sourceTransportNeighborhoodMap_mapsTo a ha x Q) Q.normalCoordinate_mapsTo (2 * p))
    (Geometric.RationalLocalPurity.Cycles.complexNormalRationalDualClass p)
  simp only [sourceTransportNeighborhoodMap_normalCoordinate, ConcreteCategory.comp_apply] at h
  exact h

end

end OAI.AlgebraicGeometry.CycleClass.Thom.NormalPair.SourceTransport.Constructions
