import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.Reduction
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.LiftedReduction

/-! # Counting Target Reduction -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Neighbor.CountingTargetReduction.CM

noncomputable section

/-! NeighborCounting's actual evaluated targets use the same unique proper
extension as the HeckeCycles specialization map. Their geometric reductions
therefore agree on the original arithmetic source, without a new
target-matching premise. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.Reduction.Lifts
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ValuativePoints.CM

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [NumberField.IsCMField E] [Field K] [NumberField K]
  {s N : ℕ} {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s}
  {iota : E →+* K} {κ : K →+* ℂ}
  {M : Over (Spec (.of K))} {U : AbelianModuli.ReferenceFamily.PEL.Objects.PELObject P iota N M}
  {B : PELModuli.IntegralModel.Base.ArithmeticBaseExtension K κ} {q : ℕ} [Fact q.Prime]
  {D : AbelianScheme.FrobeniusKernel.Integral.Construction.SplitPELReduction P iota κ M U B q}
  {R L : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field L] [Algebra R L] [IsFractionRing R L]
  {b : B.R →+* R} (z : Isogenies.NeighborCounting.Evaluated.Targets.Lifts.EvaluatedTarget D R L b)

def genericPoint : ValuativePoints.CM.genericTest (L := L) (Isogenies.NeighborCounting.Lifts.dvrBase R b) ⟶ D.integral.toOver :=
  Over.homMk z.map z.overBase

def integralPoint : Over.mk (Isogenies.NeighborCounting.Lifts.dvrBase R b) ⟶ D.integral.toOver :=
  Over.homMk z.extension z.extension_overBase

theorem extension_eq :
    (ValuativePoints.CM.evaluatedPointEquiv (Isogenies.NeighborCounting.Lifts.dvrBase R b) D.integral.toOver).symm (genericPoint z) = integralPoint z := by
  apply (ValuativePoints.CM.evaluatedPointEquiv (L := L) (Isogenies.NeighborCounting.Lifts.dvrBase R b) D.integral.toOver).injective
  rw [Equiv.apply_symm_apply]
  apply Over.OverMorphism.ext
  exact z.extension_generic.symm

variable (ρ : AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q ≃+* IsLocalRing.ResidueField R)
  (hbase : Isogenies.NeighborCounting.Lifts.ResidueCompatible D R b ρ)

theorem specialization_projection :
    (ValuativePoints.CM.specializePoint (Isogenies.NeighborCounting.Lifts.dvrBase R b) (LiftedReduction.CM.geometricResidue ρ)
      D.integral.toOver (genericPoint z)).left =
        Spec.map (CommRingCat.ofHom (LiftedReduction.CM.geometricResidue ρ)) ≫ z.extension := by
  unfold ValuativePoints.CM.specializePoint
  rw [extension_eq]
  rfl

theorem specialization_recovers_evaluated_target :
    (ValuativePoints.CM.specializePoint (Isogenies.NeighborCounting.Lifts.dvrBase R b) (LiftedReduction.CM.geometricResidue ρ)
      D.integral.toOver (genericPoint z)).left =
        (z.specialPoint hbase).left ≫ D.specialProjection := by
  rw [specialization_projection, z.specialPoint_projection hbase]
  change Spec.map (CommRingCat.ofHom (ρ.symm.toRingHom.comp (IsLocalRing.residue R))) ≫
      z.extension = Spec.map (CommRingCat.ofHom ρ.symm.toRingHom) ≫
        Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)) ≫ z.extension
  rw [← Category.assoc, ← Spec.map_comp]
  rfl

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Neighbor.CountingTargetReduction.CM
