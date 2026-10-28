import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.NormalPairFlattenChart
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.NormalPairCompactGysin
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.OpenProductTrace
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.ChartExtensionFactorization

/-! # Normal Pair Intrinsic Trace -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.NormalPairIntrinsicTrace.Constructions

noncomputable section

/-! The actual normal-pair compact Gysin map has the native manifold trace. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

set_option backward.isDefEq.respectTransparency false

variable {M N : Type} [TopologicalSpace N] {c d : ℕ} {f : M → N} {x : M}
variable (P : ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair (Fin d → ℂ) (Fin c → ℂ) f x)

abbrev normalPairTangentOpen : Opens (Fin d → ℂ) := ⟨Metric.ball 0 P.radius,Metric.isOpen_ball⟩

theorem normalPairFlattenMap_factorization :
    (TopCat.isoOfHomeo (X := TopCat.of P.openNeighborhood)
      (Y := TopCat.of (NormalPairFlattenChart.Constructions.normalPairFlattenOpen P)) (NormalPairFlattenChart.Constructions.normalPairFlattenHomeomorph P)).hom ≫
        CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of (Fin (c+d) → ℂ)) (NormalPairFlattenChart.Constructions.normalPairFlattenOpen P) =
    NormalPairProductSupport.Constructions.normalPairFirstMap P ≫ OpenProductTrace.Constructions.coordinateProductOpenMap (NormalPairProductSupport.Constructions.normalPairNormalOpen P) (normalPairTangentOpen P) ≫
      (TopCat.isoOfHomeo
        (X := TopCat.of ((Fin c → ℂ) × (Fin d → ℂ))) (Y := TopCat.of (Fin (c+d) → ℂ))
        (LocalProductCoefficient.Constructions.productFlattenCoordinates c d).toHomeomorph).hom := by
  rfl

variable [ChartedSpace (Fin (c+d) → ℂ) N] [T2Space N]
variable [IsManifold 𝓘(ℂ, Fin (c+d) → ℂ) 1 N]

theorem normalPairFirstHomeomorph_nativeTrace
    (hq : ContMDiffOn 𝓘(ℂ, Fin (c+d) → ℂ)
      𝓘(ℂ, (Fin d → ℂ) × (Fin c → ℂ)) ∞ P.ambientChart P.ambientChart.source)
    (hqi : ContMDiffOn 𝓘(ℂ, (Fin d → ℂ) × (Fin c → ℂ))
      𝓘(ℂ, Fin (c+d) → ℂ) ∞ P.ambientChart.symm P.ambientChart.target) :
    (AlgebraicTopology.Duality.Poincare.CompactSupportHomeomorph.compactSupportedCohomologyHomeomorphIso (ModuleCat.of ℚ ℚ)
      (X := TopCat.of P.openNeighborhood)
      (Y := TopCat.of (NormalPairProductSupport.Constructions.normalPairNormalOpen P × NormalPairProductSupport.Constructions.normalPairTangentSpace P))
      (NormalPairProductSupport.Constructions.normalPairFirstHomeomorph P) (2*(c+d))).hom ≫
      AlgebraicTopology.Duality.Poincare.ComplexManifoldTrace.complexManifoldTrace (c+d) (M := P.openNeighborhood) =
      OpenProductTrace.Constructions.openCoordinateProductTrace (NormalPairProductSupport.Constructions.normalPairNormalOpen P) (normalPairTangentOpen P) := by
  have ht := NormalPairFlattenChart.Constructions.normalPairFlattenExtension_trace P hq hqi
  have hf := ChartExtensionFactorization.Constructions.openExtension_chartFactorization
    (X := TopCat.of P.openNeighborhood)
    (Y := TopCat.of (NormalPairProductSupport.Constructions.normalPairNormalOpen P × NormalPairProductSupport.Constructions.normalPairTangentSpace P))
    (Z := TopCat.of ((Fin c → ℂ) × (Fin d → ℂ)))
    (W := TopCat.of (Fin (c+d) → ℂ))
    (NormalPairProductSupport.Constructions.normalPairFirstHomeomorph P)
    (OpenProductTrace.Constructions.coordinateProductOpenMap (NormalPairProductSupport.Constructions.normalPairNormalOpen P) (normalPairTangentOpen P))
    (LocalProductCoefficient.Constructions.productFlattenCoordinates c d).toHomeomorph
    (OpenProductTrace.Constructions.coordinateProductOpenMap_isOpenEmbedding (NormalPairProductSupport.Constructions.normalPairNormalOpen P) (normalPairTangentOpen P))
    (2*(c+d))
  have hc := congrArg (fun u => u ≫ AlgebraicTopology.Duality.Poincare.ComplexManifoldTrace.complexManifoldTrace (c+d) (M := Fin (c+d) → ℂ)) hf
  have h := hc.symm.trans ht
  rw [Category.assoc, Category.assoc] at h
  exact ChartExtensionFactorization.Constructions.moduleIso_trace_of_inverse
    (AlgebraicTopology.Duality.Poincare.CompactSupportHomeomorph.compactSupportedCohomologyHomeomorphIso (ModuleCat.of ℚ ℚ)
      (X := TopCat.of P.openNeighborhood)
      (Y := TopCat.of (NormalPairProductSupport.Constructions.normalPairNormalOpen P × NormalPairProductSupport.Constructions.normalPairTangentSpace P))
      (NormalPairProductSupport.Constructions.normalPairFirstHomeomorph P) (2*(c+d)))
    (OpenProductTrace.Constructions.openCoordinateProductTrace (NormalPairProductSupport.Constructions.normalPairNormalOpen P) (normalPairTangentOpen P))
    (AlgebraicTopology.Duality.Poincare.ComplexManifoldTrace.complexManifoldTrace (c+d) (M := P.openNeighborhood)) h

theorem compactHomeomorph_degreeCast {X Y : TopCat.{0}} (e : X ≃ₜ Y)
    {n m : ℕ} (h : n = m)
    (a : AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ) Y n) :
    eqToHom (congrArg (AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ) X) h)
      ((AlgebraicTopology.Duality.Poincare.CompactSupportHomeomorph.compactSupportedCohomologyHomeomorphIso (ModuleCat.of ℚ ℚ) e n).hom a) =
    (AlgebraicTopology.Duality.Poincare.CompactSupportHomeomorph.compactSupportedCohomologyHomeomorphIso (ModuleCat.of ℚ ℚ) e m).hom
      (eqToHom (congrArg (AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ) Y) h) a) := by
  subst m
  rfl

def normalPairCompactGysinTop
    (a : AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ) (TopCat.of (NormalPairProductSupport.Constructions.normalPairTangentSpace P)) (2*d)) :
    AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ) (TopCat.of P.neighborhood) (2*(c+d)) :=
  eqToHom (congrArg (AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ) (TopCat.of P.neighborhood))
    (Nat.mul_add 2 c d).symm) (NormalPairCompactGysin.Constructions.normalPairCompactGysin P (2*d) a)

theorem normalPairCompactGysinTop_eq_product
    (a : AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ) (TopCat.of (NormalPairProductSupport.Constructions.normalPairTangentSpace P)) (2*d)) :
    normalPairCompactGysinTop P a =
    (AlgebraicTopology.Duality.Poincare.CompactSupportHomeomorph.compactSupportedCohomologyHomeomorphIso (ModuleCat.of ℚ ℚ)
      (X := TopCat.of P.neighborhood)
      (Y := TopCat.of (NormalPairProductSupport.Constructions.normalPairNormalOpen P × NormalPairProductSupport.Constructions.normalPairTangentSpace P))
      (NormalPairProductSupport.Constructions.normalPairFirstHomeomorph P) (2*(c+d))).hom
      (OpenProductTrace.Constructions.openExteriorTopProduct (NormalPairProductSupport.Constructions.normalPairNormalOpen P) (normalPairTangentOpen P)
        (NestedOpenPointClass.Constructions.compactOpenPointDualClass (NormalPairProductSupport.Constructions.normalPairNormalOpen P) (Metric.mem_ball_self P.radius_pos)) a) := by
  let _ := (inferInstance : ChartedSpace (Fin (c+d) → ℂ) N)
  let _ := (inferInstance : T2Space N)
  let _ := (inferInstance : IsManifold 𝓘(ℂ, Fin (c+d) → ℂ) 1 N)
  exact compactHomeomorph_degreeCast
    (X := TopCat.of P.neighborhood)
    (Y := TopCat.of (NormalPairProductSupport.Constructions.normalPairNormalOpen P × NormalPairProductSupport.Constructions.normalPairTangentSpace P))
    (NormalPairProductSupport.Constructions.normalPairFirstHomeomorph P) (Nat.mul_add 2 c d).symm _

theorem normalPairCompactGysinTop_nativeTrace
    (hq : ContMDiffOn 𝓘(ℂ, Fin (c+d) → ℂ)
      𝓘(ℂ, (Fin d → ℂ) × (Fin c → ℂ)) ∞ P.ambientChart P.ambientChart.source)
    (hqi : ContMDiffOn 𝓘(ℂ, (Fin d → ℂ) × (Fin c → ℂ))
      𝓘(ℂ, Fin (c+d) → ℂ) ∞ P.ambientChart.symm P.ambientChart.target)
    (a : AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ) (TopCat.of (NormalPairProductSupport.Constructions.normalPairTangentSpace P)) (2*d)) :
    AlgebraicTopology.Duality.Poincare.ComplexManifoldTrace.complexManifoldTrace (c+d) (M := P.openNeighborhood) (normalPairCompactGysinTop P a) =
      AlgebraicTopology.Duality.Poincare.ComplexManifoldTrace.complexManifoldTrace d (M := normalPairTangentOpen P) a * LocalProductCoefficient.Constructions.localProductCupCoefficient c d := by
  have hp := congrArg (AlgebraicTopology.Duality.Poincare.ComplexManifoldTrace.complexManifoldTrace (c+d) (M := P.openNeighborhood))
    (normalPairCompactGysinTop_eq_product P a)
  have ht := ConcreteCategory.congr_hom (normalPairFirstHomeomorph_nativeTrace P hq hqi)
    (OpenProductTrace.Constructions.openExteriorTopProduct (NormalPairProductSupport.Constructions.normalPairNormalOpen P) (normalPairTangentOpen P)
      (NestedOpenPointClass.Constructions.compactOpenPointDualClass (NormalPairProductSupport.Constructions.normalPairNormalOpen P) (Metric.mem_ball_self P.radius_pos)) a)
  have hi := OpenProductTrace.Constructions.openExteriorTopProduct_trace (NormalPairProductSupport.Constructions.normalPairNormalOpen P) (normalPairTangentOpen P)
    (NestedOpenPointClass.Constructions.compactOpenPointDualClass (NormalPairProductSupport.Constructions.normalPairNormalOpen P) (Metric.mem_ball_self P.radius_pos)) a
  rw [NestedOpenPointClass.Constructions.compactOpenPointDualClass_trace, one_mul] at hi
  exact hp.trans (ht.trans hi)

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.NormalPairIntrinsicTrace.Constructions
