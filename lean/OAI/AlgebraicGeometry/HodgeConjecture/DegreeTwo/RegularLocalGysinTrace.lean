import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.NormalPairSourceTrace

/-! # Regular Local Gysin Trace -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.RegularLocalGysinTrace.Constructions

noncomputable section

/-! Local Gysin integration with the native source and ambient fundamental traces. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

set_option backward.isDefEq.respectTransparency false

theorem moduleIso_trace_inverse_apply {A B C : ModuleCat.{0} ℚ} (e : A ≅ B)
    (a : A ⟶ C) (b : B ⟶ C) (h : e.hom ≫ b = a) (x : B) : a (e.inv x) = b x := by
  have hx := ConcreteCategory.congr_hom h (e.inv x)
  change b (e.hom (e.inv x)) = a (e.inv x) at hx
  rw [Iso.inv_hom_id_apply] at hx
  exact hx.symm

def normalPairSourceCompactGysinTop
    {M N : Type} [TopologicalSpace M] [TopologicalSpace N] {c d : ℕ} {f : M → N} {x : M}
    (P : ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair (Fin d → ℂ) (Fin c → ℂ) f x) (hf : Topology.IsEmbedding f)
    (a : AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ) (TopCat.of (NormalPairProductSupport.Constructions.normalPairSourceOpen P hf)) (2*d)) :
    AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ) (TopCat.of P.neighborhood) (2*(c+d)) :=
  NormalPairIntrinsicTrace.Constructions.normalPairCompactGysinTop P
    ((AlgebraicTopology.Duality.Poincare.CompactSupportHomeomorph.compactSupportedCohomologyHomeomorphIso (ModuleCat.of ℚ ℚ)
      (X := TopCat.of (NormalPairProductSupport.Constructions.normalPairSourceOpen P hf)) (Y := TopCat.of (NormalPairProductSupport.Constructions.normalPairTangentBallOpen P))
      (NormalPairProductSupport.Constructions.normalPairSourceHomeomorph P hf) (2*d)).inv a)

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V 1) (x : Z.regularAnalyticSpace)
variable (P : ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair Z.regularAnalyticModel (Fin 1 → ℂ) Z.regularComplementInclusion x)

abbrev regularNormalPairDegreeEq : 2*(1+Z.regularComplexDimension) = 2*V.complexDimension :=
  congrArg (fun n => 2*n)
    ((Nat.add_comm 1 Z.regularComplexDimension).trans Z.regularComplexDimension_add_codimension)

def regularNormalPairSourceGysinToAmbient
    (a : AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ)
      (TopCat.of (NormalPairProductSupport.Constructions.normalPairSourceOpen P Z.isClosedEmbedding_regularComplementInclusion.isEmbedding))
      (2*Z.regularComplexDimension)) :
    AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ) (TopCat.of Z.regularAmbientSpace) (2*V.complexDimension) :=
  AlgebraicTopology.Duality.Poincare.CompactSupportExcision.compactSupportOpenExtension P.openNeighborhood (2*V.complexDimension)
    (eqToHom (congrArg (AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ) (TopCat.of P.neighborhood))
      (regularNormalPairDegreeEq V Z))
      (normalPairSourceCompactGysinTop P Z.isClosedEmbedding_regularComplementInclusion.isEmbedding a))

theorem regularNormalPairSourceGysin_nativeTrace
    (hq : ContMDiffOn 𝓘(ℂ, V.analyticModel)
      𝓘(ℂ, Z.regularAnalyticModel × (Fin 1 → ℂ)) ∞ P.ambientChart P.ambientChart.source)
    (hqi : ContMDiffOn 𝓘(ℂ, Z.regularAnalyticModel × (Fin 1 → ℂ))
      𝓘(ℂ, V.analyticModel) ∞ P.ambientChart.symm P.ambientChart.target)
    (a : AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ)
      (TopCat.of (NormalPairProductSupport.Constructions.normalPairSourceOpen P Z.isClosedEmbedding_regularComplementInclusion.isEmbedding))
      (2*Z.regularComplexDimension)) :
    AlgebraicTopology.Duality.Poincare.ComplexManifoldTrace.complexManifoldTrace V.complexDimension (M := P.openNeighborhood)
      (eqToHom (congrArg (AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ) (TopCat.of P.neighborhood))
        (regularNormalPairDegreeEq V Z))
        (normalPairSourceCompactGysinTop P Z.isClosedEmbedding_regularComplementInclusion.isEmbedding a)) =
    AlgebraicTopology.Duality.Poincare.ComplexManifoldTrace.complexManifoldTrace Z.regularComplexDimension
      (M := NormalPairProductSupport.Constructions.normalPairSourceOpen P Z.isClosedEmbedding_regularComplementInclusion.isEmbedding) a *
      LocalProductCoefficient.Constructions.localProductCupCoefficient 1 Z.regularComplexDimension := by
  let e := AlgebraicTopology.Duality.Poincare.CompactSupportHomeomorph.compactSupportedCohomologyHomeomorphIso (ModuleCat.of ℚ ℚ)
    (X := TopCat.of (NormalPairProductSupport.Constructions.normalPairSourceOpen P Z.isClosedEmbedding_regularComplementInclusion.isEmbedding))
    (Y := TopCat.of (NormalPairProductSupport.Constructions.normalPairTangentBallOpen P))
    (NormalPairProductSupport.Constructions.normalPairSourceHomeomorph P Z.isClosedEmbedding_regularComplementInclusion.isEmbedding)
    (2*Z.regularComplexDimension)
  have ht := PairIntrinsicTraceDimension.Constructions.regularNormalPairCompactGysinTop_nativeTrace V Z x P hq hqi (e.inv a)
  have hs := moduleIso_trace_inverse_apply e
    (AlgebraicTopology.Duality.Poincare.ComplexManifoldTrace.complexManifoldTrace Z.regularComplexDimension (M := NormalPairProductSupport.Constructions.normalPairTangentBallOpen P))
    (AlgebraicTopology.Duality.Poincare.ComplexManifoldTrace.complexManifoldTrace Z.regularComplexDimension
      (M := NormalPairProductSupport.Constructions.normalPairSourceOpen P Z.isClosedEmbedding_regularComplementInclusion.isEmbedding))
    (NormalPairSourceTrace.Constructions.regularNormalPairSourceHomeomorph_nativeTrace V Z x P hq hqi) a
  exact ht.trans (congrArg (fun r => r * LocalProductCoefficient.Constructions.localProductCupCoefficient 1 Z.regularComplexDimension) hs)

theorem regularNormalPairSourceGysinToAmbient_nativeTrace
    (hq : ContMDiffOn 𝓘(ℂ, V.analyticModel)
      𝓘(ℂ, Z.regularAnalyticModel × (Fin 1 → ℂ)) ∞ P.ambientChart P.ambientChart.source)
    (hqi : ContMDiffOn 𝓘(ℂ, Z.regularAnalyticModel × (Fin 1 → ℂ))
      𝓘(ℂ, V.analyticModel) ∞ P.ambientChart.symm P.ambientChart.target)
    (a : AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ)
      (TopCat.of (NormalPairProductSupport.Constructions.normalPairSourceOpen P Z.isClosedEmbedding_regularComplementInclusion.isEmbedding))
      (2*Z.regularComplexDimension)) :
    AlgebraicTopology.Duality.Poincare.ComplexManifoldTrace.complexManifoldTrace V.complexDimension (M := Z.regularAmbientSpace)
      (regularNormalPairSourceGysinToAmbient V Z x P a) =
    AlgebraicTopology.Duality.Poincare.ComplexManifoldTrace.complexManifoldTrace Z.regularComplexDimension (M := Z.regularAnalyticSpace)
      (AlgebraicTopology.Duality.Poincare.CompactSupportExcision.compactSupportOpenExtension (X := TopCat.of Z.regularAnalyticSpace)
        (NormalPairProductSupport.Constructions.normalPairSourceOpen P Z.isClosedEmbedding_regularComplementInclusion.isEmbedding)
        (2*Z.regularComplexDimension) a) * LocalProductCoefficient.Constructions.localProductCupCoefficient 1 Z.regularComplexDimension := by
  have hA := AlgebraicTopology.Duality.Poincare.ComplexManifoldTrace.complexManifoldTrace_open_apply V.complexDimension (M := Z.regularAmbientSpace)
    P.openNeighborhood
    (eqToHom (congrArg (AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ) (TopCat.of P.neighborhood))
      (regularNormalPairDegreeEq V Z))
      (normalPairSourceCompactGysinTop P Z.isClosedEmbedding_regularComplementInclusion.isEmbedding a))
  have hS := AlgebraicTopology.Duality.Poincare.ComplexManifoldTrace.complexManifoldTrace_open_apply Z.regularComplexDimension (M := Z.regularAnalyticSpace)
    (NormalPairProductSupport.Constructions.normalPairSourceOpen P Z.isClosedEmbedding_regularComplementInclusion.isEmbedding) a
  exact hA.trans ((regularNormalPairSourceGysin_nativeTrace V Z x P hq hqi a).trans
    (congrArg (fun r => r * LocalProductCoefficient.Constructions.localProductCupCoefficient 1 Z.regularComplexDimension) hS.symm))

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.RegularLocalGysinTrace.Constructions
