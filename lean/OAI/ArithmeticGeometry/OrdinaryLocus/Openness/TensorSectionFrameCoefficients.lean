import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.TensorUnitCoefficient

/-! # Tensor Section Frame Coefficients -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.TensorSectionFrameCoefficients.Construction

noncomputable section

/-! A tensor-frame coefficient can be read in any compatible line-bundle trivialization. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry MonoidalCategory Opposite

universe u

local instance tensorSectionFrameCoefficientsMonoidal (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  AlgebraicGeometry.SheafCohomology.Projective.Monoidal.Scheme.Modules.monoidalCategory X

theorem tensorSectionGlobalCoefficient_of_frame
    {X : Scheme.{u}} (M : X.Modules) {P Q : X.Modules}
    (a : 𝟙_ X.Modules ⟶ P) (U : X.Opens)
    [IsIso ((Scheme.Modules.pullback U.ι).map a)] (e : M ⊗ P ≅ Q)
    (f : Q.over U ≅ _root_.SheafOfModules.unit (X.ringCatSheaf.over U))
    (s : Γ(Q, ⊤)) (hs : AlgebraicGeometry.SheafCohomology.Projective.FrameSections.overTrivializationCoefficient Q U f s = 1)
    (m : Γ(M, U))
    (hm : e.hom.app U ((TensorSectionFrame.Construction.tensorByUnitSection M a).app U m) =
      Q.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op s)
    (x : Γ(M ⊗ P, ⊤)) :
    TensorSectionRestriction.Construction.tensorSectionGlobalCoefficient M a U x =
      AlgebraicGeometry.SheafCohomology.Projective.FrameSections.overTrivializationCoefficient Q U f (e.hom.app ⊤ x) • m := by
  apply (TensorSectionFrame.Construction.tensorSectionFrameAppEquiv M a U).injective
  have : IsIso (e.hom.app U) := TensorSectionFrame.Construction.moduleMap_app_isIso_of_pullback e.hom U
  apply (ConcreteCategory.bijective_of_isIso (e.hom.app U)).injective
  have ht : (TensorSectionFrame.Construction.tensorSectionFrameAppEquiv M a U) (TensorSectionRestriction.Construction.tensorSectionGlobalCoefficient M a U x) =
      (M ⊗ P).presheaf.map (homOfLE (le_top : U ≤ ⊤)).op x :=
    (TensorSectionFrame.Construction.tensorSectionFrameAppEquiv M a U).apply_symm_apply _
  rw [ht, LinearEquiv.map_smul]
  have hn := PresheafOfModules.naturality_apply e.hom.val
    (homOfLE (le_top : U ≤ ⊤)).op x
  have he := (e.hom.val.app (op U)).hom.map_smul
    (AlgebraicGeometry.SheafCohomology.Projective.FrameSections.overTrivializationCoefficient Q U f (e.hom.app ⊤ x))
    ((TensorSectionFrame.Construction.tensorSectionFrameAppEquiv M a U) m)
  have hh := AlgebraicGeometry.SheafCohomology.Projective.PositivePowerChartGenerator.restrict_eq_coefficient_smul_generator Q U f s (e.hom.app ⊤ x) hs
  exact hn.trans (hh.trans ((congrArg (fun y : Γ(Q, U) =>
    AlgebraicGeometry.SheafCohomology.Projective.FrameSections.overTrivializationCoefficient Q U f (e.hom.app ⊤ x) • y) hm).symm.trans he.symm))

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.TensorSectionFrameCoefficients.Construction
