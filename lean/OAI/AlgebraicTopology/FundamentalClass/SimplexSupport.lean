import OAI.AlgebraicTopology.FundamentalClass.SimplexGeometry
import OAI.AlgebraicTopology.FundamentalClass.IntegrationOrientation

/-! # Simplex Support -/

namespace OAI.AlgebraicTopology.FundamentalClass.SimplexSupport.IntegrationConstruction

noncomputable section

/-! The positively ordered affine simplex represents the normalized
orientation class over every compact subset of its interior. -/

open _root_.CategoryTheory Set
open OAI.AlgebraicTopology.FundamentalClass.IntegrationOrientation.Geometry
open scoped Simplicial

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def positiveInteriorChain (d : ℕ) :
    (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains (TopCat.of (Fin d → ℝ)) (SimplexGeometry.IntegrationConstruction.positiveInterior d)ᶜ).X d :=
  (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeChainProjection (TopCat.of (Fin d → ℝ)) (SimplexGeometry.IntegrationConstruction.positiveInterior d)ᶜ).f d
    (Cohomology.Singular.ChainDual.simplexChain (R := ℤ) (TopCat.toSSet.obj (TopCat.of (Fin d → ℝ)))
      (LocalSimplex.IntegrationGeometry.positiveSingularSimplex d))

theorem positiveInteriorChain_cycle (d : ℕ) :
    positiveInteriorChain d ∈ Cohomology.Singular.ChainRepresentatives.chainCycles
      (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains (TopCat.of (Fin d → ℝ)) (SimplexGeometry.IntegrationConstruction.positiveInterior d)ᶜ) d := by
  cases d with
  | zero => exact Cohomology.Singular.ChainRepresentatives.mem_chainCycles_zero _ _
  | succ d =>
    rw [Cohomology.Singular.ChainRepresentatives.mem_chainCycles_iff_succ]
    let X := TopCat.of (Fin (d + 1) → ℝ)
    let π := AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeChainProjection X (SimplexGeometry.IntegrationConstruction.positiveInterior (d + 1))ᶜ
    have hcomm := ConcreteCategory.congr_hom (π.comm (d + 1) d).symm
      (Cohomology.Singular.ChainDual.simplexChain (R := ℤ) (TopCat.toSSet.obj X) (LocalSimplex.IntegrationGeometry.positiveSingularSimplex (d + 1)))
    change π.f d ((Cohomology.Singular.Evaluation.singularScalarChains (R := ℤ) X).d (d + 1) d
      (Cohomology.Singular.ChainDual.simplexChain (R := ℤ) (TopCat.toSSet.obj X) (LocalSimplex.IntegrationGeometry.positiveSingularSimplex (d + 1)))) =
      (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X (SimplexGeometry.IntegrationConstruction.positiveInterior (d + 1))ᶜ).d (d + 1) d
        (positiveInteriorChain (d + 1)) at hcomm
    rw [← hcomm, Cohomology.Singular.ChainDual.simplexChain_boundary, map_sum]
    apply Finset.sum_eq_zero
    intro i _
    rw [map_zsmul]
    have hi : π.f d (Cohomology.Singular.ChainDual.simplexChain (R := ℤ) (TopCat.toSSet.obj X)
        ((TopCat.toSSet.obj X).δ i (LocalSimplex.IntegrationGeometry.positiveSingularSimplex (d + 1)))) = 0 := by
      apply LocalSimplex.IntegrationGeometry.relativeProjection_simplex_zero
      intro t
      exact SimplexGeometry.IntegrationConstruction.positiveSimplex_face_outside d i t
    rw [hi]
    exact zsmul_zero _

def positiveInteriorClass (d : ℕ) :
    AlgebraicGeometry.CycleClass.Geometric.HomologyWithSupports.Cycles.singularHomologyWithSupport (TopCat.of (Fin d → ℝ)) (SimplexGeometry.IntegrationConstruction.positiveInterior d) d :=
  Cohomology.Singular.ChainRepresentatives.chainClass _ d ⟨positiveInteriorChain d, positiveInteriorChain_cycle d⟩

theorem positiveInteriorClass_at_origin (d : ℕ) :
    AlgebraicGeometry.CycleClass.Geometric.LocalHomologyPresheaf.Cycles.localHomologyToPoint (TopCat.of (Fin d → ℝ)) (SimplexGeometry.IntegrationConstruction.positiveInterior d) 0
      (SimplexGeometry.IntegrationConstruction.zero_mem_positiveInterior d) d (positiveInteriorClass d) = LocalSimplex.IntegrationGeometry.positiveLocalClass d := by
  rw [positiveInteriorClass]
  change HomologicalComplex.homologyMap
    (AlgebraicGeometry.CycleClass.Geometric.LocalHomologyPresheaf.Cycles.relativeComplementChainToPoint (TopCat.of (Fin d → ℝ)) (SimplexGeometry.IntegrationConstruction.positiveInterior d) 0
      (SimplexGeometry.IntegrationConstruction.zero_mem_positiveInterior d)) d (Cohomology.Singular.ChainRepresentatives.chainClass _ d _) = _
  rw [Cohomology.Singular.EvaluationNaturality.chainClass_naturality]
  apply congrArg (Cohomology.Singular.ChainRepresentatives.chainClass _ d)
  apply Subtype.ext
  exact ConcreteCategory.congr_hom (HomologicalComplex.congr_hom
    (AlgebraicGeometry.CycleClass.Geometric.LocalHomologyPresheaf.Cycles.relativeComplementChainToPoint_projection (TopCat.of (Fin d → ℝ))
      (SimplexGeometry.IntegrationConstruction.positiveInterior d) 0 (SimplexGeometry.IntegrationConstruction.zero_mem_positiveInterior d)) d)
    (Cohomology.Singular.ChainDual.simplexChain (R := ℤ) (TopCat.toSSet.obj (TopCat.of (Fin d → ℝ)))
      (LocalSimplex.IntegrationGeometry.positiveSingularSimplex d))

section ConvexTranslation

variable (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem convexTranslation_mapsTo (U : Set E) (hU : Convex ℝ U) (h0 : (0 : E) ∈ U)
    (x : E) (hx : x ∈ U) (t : unitInterval) :
    Set.MapsTo (fun y => AlgebraicGeometry.CycleClass.Geometric.ClosedBall.Cycles.coordinateTranslationHomotopy E x (t, y)) Uᶜ ({0}ᶜ : Set E) := by
  intro y hy hz
  have hyx : y = (t : ℝ) • x := sub_eq_zero.mp hz
  have ht : (t : ℝ) • x ∈ U := by
    simpa only [smul_zero, zero_add] using
      hU h0 hx (sub_nonneg.mpr t.property.2) t.property.1 (sub_add_cancel 1 (t : ℝ))
  exact hy (hyx ▸ ht)

theorem convexPointHomologyMap_translation (U : Set E) (hU : Convex ℝ U)
    (h0 : (0 : E) ∈ U) (x : E) (hx : x ∈ U) (n : ℕ) :
    AlgebraicGeometry.CycleClass.Geometric.LocalHomologyPresheaf.Cycles.localHomologyToPoint (TopCat.of E) U x hx n ≫ (AlgebraicGeometry.CycleClass.Geometric.ClosedBall.Cycles.localTranslationHomologyIso E x n).hom =
      AlgebraicGeometry.CycleClass.Geometric.LocalHomologyPresheaf.Cycles.localHomologyToPoint (TopCat.of E) U 0 h0 n := by
  let hf : MapsTo (𝟙 (TopCat.of E)) Uᶜ ({0}ᶜ : Set E) := by
    intro y hy heq
    change y = 0 at heq
    exact hy (heq ▸ h0)
  let hg : MapsTo (TopCat.isoOfHomeo (X := TopCat.of E) (Y := TopCat.of E)
      (Homeomorph.subRight x)).hom Uᶜ ({0}ᶜ : Set E) := by
    intro y hy heq
    exact hy ((sub_eq_zero.mp heq) ▸ hx)
  let hxMap : MapsTo (𝟙 (TopCat.of E)) Uᶜ ({x}ᶜ : Set E) := by
    intro y hy heq
    change y = x at heq
    exact hy (heq ▸ hx)
  let htrans : MapsTo (TopCat.isoOfHomeo (X := TopCat.of E) (Y := TopCat.of E)
      (Homeomorph.subRight x)).hom ({x}ᶜ : Set E) ({0}ᶜ : Set E) := by
    intro y hy
    change y - x ≠ 0
    exact sub_ne_zero.mpr hy
  change AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularHomologyMap (𝟙 (TopCat.of E)) hxMap n ≫
    AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularHomologyMap (TopCat.isoOfHomeo (X := TopCat.of E) (Y := TopCat.of E)
      (Homeomorph.subRight x)).hom htrans n = AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularHomologyMap (𝟙 (TopCat.of E)) hf n
  rw [AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularHomologyMap_comp]
  exact (AlgebraicGeometry.CycleClass.Geometric.RelativeHomotopy.Cycles.relativeSingularHomologyMap_eq_of_homotopy hf hg (AlgebraicGeometry.CycleClass.Geometric.ClosedBall.Cycles.coordinateTranslationHomotopy E x)
    (convexTranslation_mapsTo E U hU h0 x hx) n).symm

end ConvexTranslation

theorem positiveInteriorClass_atPoint (d : ℕ) (x : Fin d → ℝ) (hx : x ∈ SimplexGeometry.IntegrationConstruction.positiveInterior d) :
    AlgebraicGeometry.CycleClass.Geometric.LocalHomologyPresheaf.Cycles.localHomologyToPoint (TopCat.of (Fin d → ℝ)) (SimplexGeometry.IntegrationConstruction.positiveInterior d) x hx d
      (positiveInteriorClass d) = IntegrationOrientation.Geometry.positiveCoordinateClass d x := by
  apply (AlgebraicGeometry.CycleClass.Geometric.ClosedBall.Cycles.localTranslationHomologyIso (Fin d → ℝ) x d).toLinearEquiv.injective
  change (AlgebraicGeometry.CycleClass.Geometric.ClosedBall.Cycles.localTranslationHomologyIso (Fin d → ℝ) x d).hom
    (AlgebraicGeometry.CycleClass.Geometric.LocalHomologyPresheaf.Cycles.localHomologyToPoint (TopCat.of (Fin d → ℝ)) (SimplexGeometry.IntegrationConstruction.positiveInterior d) x hx d
      (positiveInteriorClass d)) =
    (AlgebraicGeometry.CycleClass.Geometric.ClosedBall.Cycles.localTranslationHomologyIso (Fin d → ℝ) x d).hom
      ((AlgebraicGeometry.CycleClass.Geometric.ClosedBall.Cycles.localTranslationHomologyIso (Fin d → ℝ) x d).inv (LocalSimplex.IntegrationGeometry.positiveLocalClass d))
  rw [CategoryTheory.Iso.inv_hom_id_apply]
  have h := ConcreteCategory.congr_hom
    (convexPointHomologyMap_translation (Fin d → ℝ) (SimplexGeometry.IntegrationConstruction.positiveInterior d)
      (SimplexGeometry.IntegrationConstruction.positiveInterior_convex d) (SimplexGeometry.IntegrationConstruction.zero_mem_positiveInterior d) x hx d) (positiveInteriorClass d)
  exact h.trans (positiveInteriorClass_at_origin d)

theorem positiveInteriorClass_restrict_compact (d : ℕ) (K : Set (Fin d → ℝ))
    (hK : IsCompact K) (hKs : K ⊆ SimplexGeometry.IntegrationConstruction.positiveInterior d) :
    AlgebraicGeometry.CycleClass.Geometric.CompactSupportAssembly.Cycles.homologyWithSupportRestriction (TopCat.of (Fin d → ℝ)) hKs d (positiveInteriorClass d) =
      IntegrationOrientation.Geometry.coordinateCompactClass d K hK := by
  apply RealSupport.IntegrationGeometry.realManifold_compactSupport_point_ext d K hK
  intro x hx
  rw [AlgebraicGeometry.CycleClass.Geometric.FiniteSupportAssembly.Cycles.homologyWithSupportRestriction_toPoint_apply, positiveInteriorClass_atPoint,
    IntegrationOrientation.Geometry.coordinateCompactClass_atPoint]

end

end OAI.AlgebraicTopology.FundamentalClass.SimplexSupport.IntegrationConstruction
