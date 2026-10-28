import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Affine.DualLiftDeformedPullback
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Affine.ChartLiftInclusion
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Affine.ConormalLiftDifference

/-! # Conormal Deformed Pullback -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Affine.ConormalDeformedPullback

noncomputable section

/-! For actual lifts through a smooth affine chart, conormal
discrepancies pull back by the reduced coefficient map even when the
map between the dual-number tests is itself deformed. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

attribute [local implicit_reducible] EtaleSplittingAt.EtaleSplitting.affineOver

variable (A : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral A.left] [Smooth A.hom] [GrpObj A]
    (B : CommAlgCat ℂ) [IsDomain B] [Algebra.Smooth ℂ B]
    (i : EtaleSplittingAt.EtaleSplitting.affineOver ℂ B ⟶ A) [IsOpenImmersion i.left]
    (C : Type) [CommRing C] [Algebra ℂ C] [Algebra B C] [IsScalarTower ℂ B C]
    [Algebra.FiniteType ℂ C] [IsReduced C]
    (f : DualNumber B →ₐ[ℂ] DualNumber C)
    (hred : ∀ u, (f u).fst = algebraMap B C u.fst)

def affineChartDeformedPullbackLift
    (u : {u : EtaleSplittingAt.EtaleSplitting.affineOver ℂ (DualNumber B) ⟶ EtaleSplittingAt.EtaleSplitting.affineOver ℂ B //
      Dual.CoefficientSchemeTests.dualCoefficientOrigin ℂ B ≫ u = AlgebraAutomorphismNaturality.affineOverAlgHom ℂ B B (IsScalarTower.toAlgHom ℂ B B)}) :
    {u : EtaleSplittingAt.EtaleSplitting.affineOver ℂ (DualNumber C) ⟶ A //
      Dual.CoefficientSchemeTests.dualCoefficientOrigin ℂ C ≫ u = ChartCoefficientConormal.affineChartCoefficientPoint ℂ B C A i} :=
  ChartLiftInclusion.affineChartCoefficientLiftInclusion ℂ B C A i (DualLiftDeformedPullback.affineDualLiftDeformedPullback ℂ B C f hred u)

omit [IsIntegral A.left] [Smooth A.hom] [GrpObj A] [IsDomain B] [Algebra.Smooth ℂ B]
    [Algebra.FiniteType ℂ C] [IsReduced C] in
theorem affineChartDeformedPullbackLift_value
    (u : {u : EtaleSplittingAt.EtaleSplitting.affineOver ℂ (DualNumber B) ⟶ EtaleSplittingAt.EtaleSplitting.affineOver ℂ B //
      Dual.CoefficientSchemeTests.dualCoefficientOrigin ℂ B ≫ u = AlgebraAutomorphismNaturality.affineOverAlgHom ℂ B B (IsScalarTower.toAlgHom ℂ B B)}) :
    (affineChartDeformedPullbackLift A B i C f hred u).val =
      AlgebraAutomorphismNaturality.affineOverAlgHom ℂ (DualNumber B) (DualNumber C) f ≫ (u.val ≫ i) := by
  change (DualLiftDeformedPullback.affineDualLiftDeformedPullback ℂ B C f hred u).val ≫ i = _
  rw [DualLiftDeformedPullback.affineDualLiftDeformedPullback_value, Category.assoc]

theorem affineConormalDeformedPullback
    (heps : f DualNumber.eps = DualNumber.eps)
    (u v : {u : EtaleSplittingAt.EtaleSplitting.affineOver ℂ (DualNumber B) ⟶ EtaleSplittingAt.EtaleSplitting.affineOver ℂ B //
      Dual.CoefficientSchemeTests.dualCoefficientOrigin ℂ B ≫ u = AlgebraAutomorphismNaturality.affineOverAlgHom ℂ B B (IsScalarTower.toAlgHom ℂ B B)})
    (z : Constructed.IdentityConormal.constructedIdentityConormal ℂ A) :
    Constructed.IdentityConormal.constructedIdentityLiftConormalEquiv ℂ A C (affineChartDeformedPullbackLift A B i C f hred u).val
        ⟨(affineChartDeformedPullbackLift A B i C f hred v).val,
          (affineChartDeformedPullbackLift A B i C f hred v).property.trans
            (affineChartDeformedPullbackLift A B i C f hred u).property.symm⟩ z =
      algebraMap B C (Constructed.IdentityConormal.constructedIdentityLiftConormalEquiv ℂ A B
        (ChartLiftInclusion.affineChartCoefficientLiftInclusion ℂ B B A i u).val
        ⟨(ChartLiftInclusion.affineChartCoefficientLiftInclusion ℂ B B A i v).val,
          (ChartLiftInclusion.affineChartCoefficientLiftInclusion ℂ B B A i v).property.trans
            (ChartLiftInclusion.affineChartCoefficientLiftInclusion ℂ B B A i u).property.symm⟩ z) := by
  let u' := affineChartDeformedPullbackLift A B i C f hred u
  let v' := affineChartDeformedPullbackLift A B i C f hred v
  let u₀ := ChartLiftInclusion.affineChartCoefficientLiftInclusion ℂ B B A i u
  let v₀ := ChartLiftInclusion.affineChartCoefficientLiftInclusion ℂ B B A i v
  let d := DualLiftConormal.affineDualLiftDerivationEquiv ℂ B B v - DualLiftConormal.affineDualLiftDerivationEquiv ℂ B B u
  have hd : ChartCoefficientConormal.affineChartCoefficientLiftDerivationEquiv ℂ B C A i v' -
      ChartCoefficientConormal.affineChartCoefficientLiftDerivationEquiv ℂ B C A i u' =
        Dual.CoefficientLiftNaturality.coefficientDerivationMap ℂ B B C (IsScalarTower.toAlgHom B B C) d := by
    dsimp only [u', v', affineChartDeformedPullbackLift]
    rw [ChartLiftInclusion.affineChartCoefficientLiftInclusion_derivation, ChartLiftInclusion.affineChartCoefficientLiftInclusion_derivation]
    apply Derivation.ext
    intro b
    exact DualLiftDeformedPullback.affineDualLiftDeformedPullback_difference ℂ B C f hred heps v u b
  have hd₀ : ChartCoefficientConormal.affineChartCoefficientLiftDerivationEquiv ℂ B B A i v₀ -
      ChartCoefficientConormal.affineChartCoefficientLiftDerivationEquiv ℂ B B A i u₀ = d := by
    rw [ChartLiftInclusion.affineChartCoefficientLiftInclusion_derivation, ChartLiftInclusion.affineChartCoefficientLiftInclusion_derivation]
  have hc := congrArg (fun w => w z) (ConormalLiftDifference.affineConormalLiftDifference A B i C u' v')
  have hc₀ := congrArg (fun w => w z) (ConormalLiftDifference.affineConormalLiftDifference A B i B u₀ v₀)
  rw [hd] at hc
  rw [hd₀] at hc₀
  exact hc.trans ((ChartConormalNaturality.affineChartCoefficientConormalEquiv_natural ℂ B B C
    (IsScalarTower.toAlgHom B B C) A i d z).trans (congrArg (algebraMap B C) hc₀.symm))

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Affine.ConormalDeformedPullback
