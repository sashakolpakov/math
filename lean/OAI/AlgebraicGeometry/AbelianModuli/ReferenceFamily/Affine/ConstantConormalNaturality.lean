import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Affine.ConstantConormalLift
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Affine.ChartLiftInclusion
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.UnitRatioLogarithms

/-! # Constant Conormal Naturality -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Affine.ConstantConormalNaturality

noncomputable section

section

/-! The original affine restriction of an infinitesimal group
translation has its constant conormal derivation as second coefficient.
Its ratio with the original projection therefore gives exactly the
line-frame logarithmic coefficient used in native H1. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

attribute [local implicit_reducible] EtaleSplittingAt.EtaleSplitting.affineOver

variable (G : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral G.left] [Smooth G.hom] [GrpObj G]
    (B : CommAlgCat ℂ) (i : EtaleSplittingAt.EtaleSplitting.affineOver ℂ B ⟶ G) [IsOpenImmersion i.left]
    (l : Constructed.IdentityConormal.constructedIdentityConormal ℂ G →ₗ[ℂ] ℂ)

def affineConstantConormalOpenLift :
    {f : EtaleSplittingAt.EtaleSplitting.affineOver ℂ (DualNumber B) ⟶ EtaleSplittingAt.EtaleSplitting.affineOver ℂ B // Dual.CoefficientSchemeTests.dualCoefficientOrigin ℂ B ≫ f =
      AlgebraAutomorphismNaturality.affineOverAlgHom ℂ B B (IsScalarTower.toAlgHom ℂ B B)} :=
  (Open.ImmersionLiftFibers.openImmersionLiftFiberEquiv (Dual.CoefficientSchemeTests.dualCoefficientOrigin ℂ B) i
    (AlgebraAutomorphismNaturality.affineOverAlgHom ℂ B B (IsScalarTower.toAlgHom ℂ B B))).symm (ConstantConormalLift.affineConstantConormalLift G B i l)

omit [IsIntegral G.left] in
theorem affineConstantConormalOpenLift_inclusion :
    (affineConstantConormalOpenLift G B i l).val ≫ i = (ConstantConormalLift.affineConstantConormalLift G B i l).val :=
  congrArg Subtype.val ((Open.ImmersionLiftFibers.openImmersionLiftFiberEquiv (Dual.CoefficientSchemeTests.dualCoefficientOrigin ℂ B) i
    (AlgebraAutomorphismNaturality.affineOverAlgHom ℂ B B (IsScalarTower.toAlgHom ℂ B B))).apply_symm_apply (ConstantConormalLift.affineConstantConormalLift G B i l))

def affineTranslationCoefficients : B →ₐ[ℂ] DualNumber B :=
  OverMorphismAlgebra.affineOverMorphismAlgebra ℂ (DualNumber B) B (affineConstantConormalOpenLift G B i l).val

omit [IsIntegral G.left] in
theorem affineTranslationCoefficients_fst (a : B) : (affineTranslationCoefficients G B i l a).fst = a :=
  AlgHom.congr_fun ((DualLiftReduction.affineDualLift_reduction_iff ℂ B B (IsScalarTower.toAlgHom ℂ B B)
    (affineConstantConormalOpenLift G B i l).val).mp (affineConstantConormalOpenLift G B i l).property) a

theorem affineTranslationCoefficients_snd (a : B) :
    (affineTranslationCoefficients G B i l a).snd =
      (PresentationConormalLinearity.affinePresentationConormalLinearEquiv G B i).symm (ConormalUnitLogCoordinates.coefficientCovector B l) a := by
  have he : DualLiftConormal.affineDualLiftDerivationEquiv ℂ B B (affineConstantConormalOpenLift G B i l) =
      ChartCoefficientConormal.affineChartCoefficientLiftDerivationEquiv ℂ B B G i (ConstantConormalLift.affineConstantConormalLift G B i l) := rfl
  exact (DualLiftConormal.affineDualLiftDerivationEquiv_apply ℂ B B (affineConstantConormalOpenLift G B i l) a).symm.trans
    (Derivation.congr_fun (he.trans (ConstantConormalLift.affineConstantConormalLift_derivation G B i l)) a)

theorem affineTranslationUnitRatio_coefficient (u : Bˣ) :
    (Units.map (affineTranslationCoefficients G B i l).toMonoidHom u /
      Units.map (TrivSqZeroExt.inlAlgHom ℂ B B).toMonoidHom u).val.snd =
        CoefficientUnitLogarithms.coefficientUnitLog ((PresentationConormalLinearity.affinePresentationConormalLinearEquiv G B i).symm (ConormalUnitLogCoordinates.coefficientCovector B l)) u :=
  Dual.UnitRatioLogarithms.dualUnitPullbackRatio_coefficient (affineTranslationCoefficients G B i l).toRingHom
    (TrivSqZeroExt.inlAlgHom ℂ B B).toRingHom (affineTranslationCoefficients_fst G B i l)
    (fun _ => rfl) _ (fun a => (sub_zero _).trans (affineTranslationCoefficients_snd G B i l a)) u

end

/-! Constant conormal derivations and their original unit logarithms
commute with every actual etale map between affine presentations of
opens in the group. This includes changes to canonical section rings. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable (G : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral G.left] [Smooth G.hom] [GrpObj G]
    (B : CommAlgCat ℂ) (i : EtaleSplittingAt.EtaleSplitting.affineOver ℂ B ⟶ G) [IsOpenImmersion i.left]
    (D : CommAlgCat ℂ) (j : EtaleSplittingAt.EtaleSplitting.affineOver ℂ D ⟶ G) [IsOpenImmersion j.left]
    (q : B →ₐ[ℂ] D) (hq : q.toRingHom.Etale) (hi : AlgebraAutomorphismNaturality.affineOverAlgHom ℂ B D q ≫ i = j)
    (l : Constructed.IdentityConormal.constructedIdentityConormal ℂ G →ₗ[ℂ] ℂ)

include hq hi

theorem affineConstantConormalDerivation_natural :
    EtaleHomDerivation.etaleAlgHomDerivationLinear q hq
      ((PresentationConormalLinearity.affinePresentationConormalLinearEquiv G B i).symm (ConormalUnitLogCoordinates.coefficientCovector B l)) =
      (PresentationConormalLinearity.affinePresentationConormalLinearEquiv G D j).symm (ConormalUnitLogCoordinates.coefficientCovector D l) := by
  apply (PresentationConormalLinearity.affinePresentationConormalLinearEquiv G D j).injective
  apply LinearMap.ext
  intro z
  rw [PresentationConormalLinearity.affinePresentationConormalLinearEquiv_natural G B i D j q hq hi,
    LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  exact q.commutes (l z)

theorem affineConstantConormalUnitLog_natural (u : Bˣ) :
    CoefficientUnitLogarithms.coefficientUnitLog ((PresentationConormalLinearity.affinePresentationConormalLinearEquiv G D j).symm (ConormalUnitLogCoordinates.coefficientCovector D l))
      (Units.map q.toMonoidHom u) =
      q (CoefficientUnitLogarithms.coefficientUnitLog ((PresentationConormalLinearity.affinePresentationConormalLinearEquiv G B i).symm (ConormalUnitLogCoordinates.coefficientCovector B l)) u) := by
  have he (a : B) :
      (PresentationConormalLinearity.affinePresentationConormalLinearEquiv G D j).symm (ConormalUnitLogCoordinates.coefficientCovector D l) (q a) =
      q ((PresentationConormalLinearity.affinePresentationConormalLinearEquiv G B i).symm (ConormalUnitLogCoordinates.coefficientCovector B l) a) := by
    rw [← affineConstantConormalDerivation_natural G B i D j q hq hi l]
    exact EtaleHomDerivation.etaleAlgHomDerivationLinear_map q hq
      ((PresentationConormalLinearity.affinePresentationConormalLinearEquiv G B i).symm (ConormalUnitLogCoordinates.coefficientCovector B l)) a
  exact CoefficientUnitLogarithms.coefficientUnitLog_map q q (fun _ => rfl) _ _ he u

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Affine.ConstantConormalNaturality
