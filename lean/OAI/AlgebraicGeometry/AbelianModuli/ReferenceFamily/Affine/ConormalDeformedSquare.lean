import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Affine.ConormalDeformedPullback
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Constructed.ConormalCongruence

/-! # Conormal Deformed Square -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Affine.ConormalDeformedSquare

noncomputable section

/-! The deformed pullback comparison applies directly to original
group-valued chart lifts and any actual maps identified with their
scheme pullbacks. The conormal coordinate retains both original maps. -/

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
    (heps : f DualNumber.eps = DualNumber.eps)

include hred heps

theorem affineConormalDeformedPullback_originalSquare
    (u v : {u : EtaleSplittingAt.EtaleSplitting.affineOver ℂ (DualNumber B) ⟶ A //
      Dual.CoefficientSchemeTests.dualCoefficientOrigin ℂ B ≫ u = ChartCoefficientConormal.affineChartCoefficientPoint ℂ B B A i})
    (u' v' : EtaleSplittingAt.EtaleSplitting.affineOver ℂ (DualNumber C) ⟶ A)
    (h' : Dual.CoefficientSchemeTests.dualCoefficientOrigin ℂ C ≫ v' = Dual.CoefficientSchemeTests.dualCoefficientOrigin ℂ C ≫ u')
    (hu : AlgebraAutomorphismNaturality.affineOverAlgHom ℂ (DualNumber B) (DualNumber C) f ≫ u.val = u')
    (hv : AlgebraAutomorphismNaturality.affineOverAlgHom ℂ (DualNumber B) (DualNumber C) f ≫ v.val = v')
    (z : Constructed.IdentityConormal.constructedIdentityConormal ℂ A) :
    Constructed.IdentityConormal.constructedIdentityLiftConormalEquiv ℂ A C u' ⟨v', h'⟩ z =
      algebraMap B C (Constructed.IdentityConormal.constructedIdentityLiftConormalEquiv ℂ A B u.val
        ⟨v.val, v.property.trans u.property.symm⟩ z) := by
  let E := Open.ImmersionLiftFibers.openImmersionLiftFiberEquiv (Dual.CoefficientSchemeTests.dualCoefficientOrigin ℂ B) i
    (AlgebraAutomorphismNaturality.affineOverAlgHom ℂ B B (IsScalarTower.toAlgHom ℂ B B))
  let a := E.symm u
  let b := E.symm v
  have ha : ChartLiftInclusion.affineChartCoefficientLiftInclusion ℂ B B A i a = u := E.apply_symm_apply u
  have hb : ChartLiftInclusion.affineChartCoefficientLiftInclusion ℂ B B A i b = v := E.apply_symm_apply v
  let a' := ConormalDeformedPullback.affineChartDeformedPullbackLift A B i C f hred a
  let b' := ConormalDeformedPullback.affineChartDeformedPullbackLift A B i C f hred b
  have ha' : a'.val = u' := by
    have H := ConormalDeformedPullback.affineChartDeformedPullbackLift_value A B i C f hred a
    have H₀ := congrArg Subtype.val ha
    exact H.trans ((congrArg (fun t => AlgebraAutomorphismNaturality.affineOverAlgHom ℂ (DualNumber B) (DualNumber C) f ≫ t) H₀).trans hu)
  have hb' : b'.val = v' := by
    have H := ConormalDeformedPullback.affineChartDeformedPullbackLift_value A B i C f hred b
    have H₀ := congrArg Subtype.val hb
    exact H.trans ((congrArg (fun t => AlgebraAutomorphismNaturality.affineOverAlgHom ℂ (DualNumber B) (DualNumber C) f ≫ t) H₀).trans hv)
  have hL := Constructed.ConormalCongruence.constructedIdentityLiftConormalEquiv_congr ℂ A C a'.val u'
    ⟨b'.val, b'.property.trans a'.property.symm⟩ ⟨v', h'⟩ ha' hb'
  have hR := Constructed.ConormalCongruence.constructedIdentityLiftConormalEquiv_congr ℂ A B
    (ChartLiftInclusion.affineChartCoefficientLiftInclusion ℂ B B A i a).val u.val
    ⟨(ChartLiftInclusion.affineChartCoefficientLiftInclusion ℂ B B A i b).val,
      (ChartLiftInclusion.affineChartCoefficientLiftInclusion ℂ B B A i b).property.trans
        (ChartLiftInclusion.affineChartCoefficientLiftInclusion ℂ B B A i a).property.symm⟩
    ⟨v.val, v.property.trans u.property.symm⟩ (congrArg Subtype.val ha) (congrArg Subtype.val hb)
  exact (congrArg (fun w => w z) hL).symm.trans
    ((ConormalDeformedPullback.affineConormalDeformedPullback A B i C f hred heps a b z).trans
      (congrArg (algebraMap B C) (congrArg (fun w => w z) hR)))

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Affine.ConormalDeformedSquare
