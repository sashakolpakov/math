import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.NormalPairProductSupport
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.LocalProductCoefficient
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.SmoothOpenChartTrace

/-! # Normal Pair Flatten Chart -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.NormalPairFlattenChart.Constructions

noncomputable section

/-! Smooth flattened charts for the actual normal-pair neighborhood. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

set_option backward.isDefEq.respectTransparency false

variable {M N : Type} [TopologicalSpace N] {c d : ℕ} {f : M → N} {x : M}
variable (P : ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair (Fin d → ℂ) (Fin c → ℂ) f x)

def normalPairFlattenCoordinates :
    ((Fin d → ℂ) × (Fin c → ℂ)) ≃L[ℂ] (Fin (c+d) → ℂ) :=
  (ContinuousLinearEquiv.prodComm ℂ (Fin d → ℂ) (Fin c → ℂ)).trans
    (LocalProductCoefficient.Constructions.productFlattenCoordinates c d)

def normalPairFlattenChart : OpenPartialHomeomorph N (Fin (c+d) → ℂ) :=
  P.ambientChart.transHomeomorph (normalPairFlattenCoordinates (c := c) (d := d)).toHomeomorph

def normalPairFlattenOpen : Opens (Fin (c+d) → ℂ) :=
  ⟨normalPairFlattenCoordinates (c := c) (d := d) ''
    (Metric.ball (0 : Fin d → ℂ) P.radius ×ˢ Metric.ball (0 : Fin c → ℂ) P.radius),
    (normalPairFlattenCoordinates (c := c) (d := d)).toHomeomorph.isOpenMap _
      (Metric.isOpen_ball.prod Metric.isOpen_ball)⟩

theorem normalPairFlattenChart_source :
    (P.openNeighborhood : Set N) ⊆ (normalPairFlattenChart P).source :=
  P.neighborhood_subset_source

theorem normalPairFlattenChart_image :
    normalPairFlattenChart P '' (P.openNeighborhood : Set N) = normalPairFlattenOpen P := by
  change (normalPairFlattenCoordinates (c := c) (d := d) ∘ P.ambientChart) '' P.neighborhood = _
  exact (Set.image_image (normalPairFlattenCoordinates (c := c) (d := d))
    P.ambientChart P.neighborhood).symm.trans
      (congrArg (fun S => normalPairFlattenCoordinates (c := c) (d := d) '' S)
        (P.ambientChart.image_symm_image_of_subset_target P.product_subset_target))

abbrev normalPairFlattenHomeomorph : P.openNeighborhood ≃ₜ normalPairFlattenOpen P :=
  SmoothOpenChartTrace.Constructions.openChartHomeomorph (normalPairFlattenChart P) P.openNeighborhood (normalPairFlattenOpen P)
    (normalPairFlattenChart_source P) (normalPairFlattenChart_image P)

variable [ChartedSpace (Fin (c+d) → ℂ) N]

theorem normalPairFlattenChart_smooth
    (hq : ContMDiffOn 𝓘(ℂ, Fin (c+d) → ℂ)
      𝓘(ℂ, (Fin d → ℂ) × (Fin c → ℂ)) ∞ P.ambientChart P.ambientChart.source)
    (hqi : ContMDiffOn 𝓘(ℂ, (Fin d → ℂ) × (Fin c → ℂ))
      𝓘(ℂ, Fin (c+d) → ℂ) ∞ P.ambientChart.symm P.ambientChart.target) :
    ContMDiffOn 𝓘(ℂ, Fin (c+d) → ℂ) 𝓘(ℂ, Fin (c+d) → ℂ) ∞
      (normalPairFlattenChart P) (normalPairFlattenChart P).source ∧
    ContMDiffOn 𝓘(ℂ, Fin (c+d) → ℂ) 𝓘(ℂ, Fin (c+d) → ℂ) ∞
      (normalPairFlattenChart P).symm (normalPairFlattenChart P).target := by
  let k := normalPairFlattenCoordinates (c := c) (d := d)
  constructor
  · change ContMDiffOn _ _ ∞ (k ∘ P.ambientChart) P.ambientChart.source
    exact (k.contDiff (n := ∞)).contMDiff.comp_contMDiffOn hq
  · change ContMDiffOn _ _ ∞ (P.ambientChart.symm ∘ k.symm) (k.symm ⁻¹' P.ambientChart.target)
    exact hqi.comp (k.symm.contDiff (n := ∞)).contMDiff.contMDiffOn (fun _ hx => hx)

variable [T2Space N] [IsManifold 𝓘(ℂ, Fin (c+d) → ℂ) 1 N]

theorem normalPairFlattenExtension_trace
    (hq : ContMDiffOn 𝓘(ℂ, Fin (c+d) → ℂ)
      𝓘(ℂ, (Fin d → ℂ) × (Fin c → ℂ)) ∞ P.ambientChart P.ambientChart.source)
    (hqi : ContMDiffOn 𝓘(ℂ, (Fin d → ℂ) × (Fin c → ℂ))
      𝓘(ℂ, Fin (c+d) → ℂ) ∞ P.ambientChart.symm P.ambientChart.target) :
    OpenEmbeddingExtension.Constructions.openEmbeddingCompactExtension
      ((TopCat.isoOfHomeo (X := TopCat.of P.openNeighborhood)
        (Y := TopCat.of (normalPairFlattenOpen P)) (normalPairFlattenHomeomorph P)).hom ≫
          CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of (Fin (c+d) → ℂ)) (normalPairFlattenOpen P))
      ((normalPairFlattenOpen P).isOpen.isOpenEmbedding_subtypeVal.comp
        (normalPairFlattenHomeomorph P).isOpenEmbedding) (2*(c+d)) ≫
      AlgebraicTopology.Duality.Poincare.ComplexManifoldTrace.complexManifoldTrace (c+d) (M := Fin (c+d) → ℂ) =
      AlgebraicTopology.Duality.Poincare.ComplexManifoldTrace.complexManifoldTrace (c+d) (M := P.openNeighborhood) := by
  have hs := normalPairFlattenChart_smooth P hq hqi
  exact SmoothOpenChartTrace.Constructions.complexManifoldTrace_openChartExtension (normalPairFlattenChart P)
    P.openNeighborhood (normalPairFlattenOpen P) (normalPairFlattenChart_source P)
    (normalPairFlattenChart_image P) hs.1 hs.2

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.NormalPairFlattenChart.Constructions
