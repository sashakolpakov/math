import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.ExteriorCupOpenExtension
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.CompactProductTrace

/-! # Open Product Trace -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.OpenProductTrace.Constructions

noncomputable section

/-! Actual exterior-product integration on open complex coordinate neighborhoods. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace
open OAI.AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels

set_option backward.isDefEq.respectTransparency false

theorem openEmbeddingCompactExtension_degreeCast {X Y : TopCat.{0}} [T2Space Y]
    (f : X ⟶ Y) (hf : Topology.IsOpenEmbedding f) {n m : ℕ} (h : n = m)
    (a : AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ) X n) :
    OpenEmbeddingExtension.Constructions.openEmbeddingCompactExtension f hf m
      (eqToHom (congrArg (AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ) X) h) a) =
    eqToHom (congrArg (AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ) Y) h)
      (OpenEmbeddingExtension.Constructions.openEmbeddingCompactExtension f hf n a) := by
  subst m
  rfl

variable {c d : ℕ} (U : Opens (Fin c → ℂ)) (V : Opens (Fin d → ℂ))

def coordinateProductOpenMap :
    TopCat.of (U×V) ⟶ TopCat.of ((Fin c → ℂ) × (Fin d → ℂ)) :=
  AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.productSpace.map ((CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of (Fin c → ℂ)) U,
    CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of (Fin d → ℂ)) V) :
    (TopCat.of U,TopCat.of V) ⟶ (TopCat.of (Fin c → ℂ),TopCat.of (Fin d → ℂ)))

theorem coordinateProductOpenMap_isOpenEmbedding :
    Topology.IsOpenEmbedding (coordinateProductOpenMap U V) :=
  U.isOpen.isOpenEmbedding_subtypeVal.prodMap V.isOpen.isOpenEmbedding_subtypeVal

def openCoordinateProductTrace :
    AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ) (TopCat.of (U×V)) (2*(c+d)) ⟶ ModuleCat.of ℚ ℚ :=
  OpenEmbeddingExtension.Constructions.openEmbeddingCompactExtension (coordinateProductOpenMap U V)
    (coordinateProductOpenMap_isOpenEmbedding U V) (2*(c+d)) ≫ CompactProductTrace.Constructions.compactProductCoordinateTrace c d

def openExteriorTopProduct
    (a : AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ) (TopCat.of U) (2*c))
    (b : AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ) (TopCat.of V) (2*d)) :
    AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ) (TopCat.of (U×V)) (2*(c+d)) :=
  eqToHom (congrArg (AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ)
    (TopCat.of (U×V))) (Nat.mul_add 2 c d).symm)
    (CompactExteriorCup.Constructions.compactExteriorCup (TopCat.of U) (TopCat.of V) (2*c) (2*d) a b)

theorem openExteriorTopProduct_extension
    (a : AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ) (TopCat.of U) (2*c))
    (b : AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ) (TopCat.of V) (2*d)) :
    OpenEmbeddingExtension.Constructions.openEmbeddingCompactExtension (coordinateProductOpenMap U V)
      (coordinateProductOpenMap_isOpenEmbedding U V) (2*(c+d)) (openExteriorTopProduct U V a b) =
    CompactProductTrace.Constructions.compactExteriorTopProduct c d
      (OpenEmbeddingExtension.Constructions.openEmbeddingCompactExtension (CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of (Fin c → ℂ)) U)
        U.isOpen.isOpenEmbedding_subtypeVal (2*c) a)
      (OpenEmbeddingExtension.Constructions.openEmbeddingCompactExtension (CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of (Fin d → ℂ)) V)
        V.isOpen.isOpenEmbedding_subtypeVal (2*d) b) := by
  have he := ExteriorCupOpenExtension.Constructions.compactExteriorCup_openExtension
    (CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of (Fin c → ℂ)) U)
    (CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of (Fin d → ℂ)) V)
    U.isOpen.isOpenEmbedding_subtypeVal V.isOpen.isOpenEmbedding_subtypeVal (2*c) (2*d) a b
  have hc := congrArg
    (fun z : AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ)
      (TopCat.of ((Fin c → ℂ) × (Fin d → ℂ))) (2*c+2*d) =>
      eqToHom (congrArg (AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ)
        (TopCat.of ((Fin c → ℂ) × (Fin d → ℂ)))) (Nat.mul_add 2 c d).symm) z) he
  exact (openEmbeddingCompactExtension_degreeCast (coordinateProductOpenMap U V)
    (coordinateProductOpenMap_isOpenEmbedding U V) (Nat.mul_add 2 c d).symm
    (CompactExteriorCup.Constructions.compactExteriorCup (TopCat.of U) (TopCat.of V) (2*c) (2*d) a b)).trans hc

theorem openExteriorTopProduct_trace
    (a : AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ) (TopCat.of U) (2*c))
    (b : AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ) (TopCat.of V) (2*d)) :
    openCoordinateProductTrace U V (openExteriorTopProduct U V a b) =
      AlgebraicTopology.Duality.Poincare.ComplexManifoldTrace.complexManifoldTrace c (M := U) a * AlgebraicTopology.Duality.Poincare.ComplexManifoldTrace.complexManifoldTrace d (M := V) b *
        LocalProductCoefficient.Constructions.localProductCupCoefficient c d := by
  change CompactProductTrace.Constructions.compactProductCoordinateTrace c d
    (OpenEmbeddingExtension.Constructions.openEmbeddingCompactExtension (coordinateProductOpenMap U V)
      (coordinateProductOpenMap_isOpenEmbedding U V) (2*(c+d)) (openExteriorTopProduct U V a b)) = _
  rw [openExteriorTopProduct_extension]
  rw [CompactProductTrace.Constructions.compactExteriorTopProduct_trace, OpenEmbeddingExtension.Constructions.openEmbeddingCompactExtension_openSubspace,
    OpenEmbeddingExtension.Constructions.openEmbeddingCompactExtension_openSubspace]
  exact congrArg₂ (fun x y : ℚ => x*y*LocalProductCoefficient.Constructions.localProductCupCoefficient c d)
    (AlgebraicTopology.Duality.Poincare.ComplexManifoldTrace.complexManifoldTrace_open_apply c (M := Fin c → ℂ) U a)
    (AlgebraicTopology.Duality.Poincare.ComplexManifoldTrace.complexManifoldTrace_open_apply d (M := Fin d → ℂ) V b)

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.OpenProductTrace.Constructions
