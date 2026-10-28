import OAI.NumberTheory.PadicHodge.IntegralComparison.Independent.QuasicoherentGluing

/-! # Open Generators -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Independent.OpenGenerators

noncomputable section

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry _root_.TopologicalSpace

universe u

def restrict {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j]
    {M : Y.Modules} (G : M.GeneratingSections) : (M.restrict j).GeneratingSections :=
  @SheafOfModules.GeneratingSections.map _ _ _ _ _ _ _ _ _ _ _ _ _ G
    (Scheme.Modules.restrictFunctor j)
    (Scheme.Modules.restrictAdjunction j).leftAdjoint_preservesColimits
    (Scheme.Modules.restrictUnitIso j).symm

theorem restrict_finite {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j]
    {M : Y.Modules} (G : M.GeneratingSections) [hG : G.IsFiniteType] :
    (OpenGenerators.restrict j G).IsFiniteType := by
  constructor
  exact hG.finite

def fromOver {X : Scheme.{u}} (M : X.Modules) (U : X.Opens)
    (G : (M.over U).GeneratingSections) : (M.restrict U.ι).GeneratingSections := by
  let E := Scheme.Modules.overEquiv U
  let hPres : PreservesColimitsOfSize.{u, u} E.functor :=
    E.toAdjunction.leftAdjoint_preservesColimits
  let H := @SheafOfModules.GeneratingSections.map _ _ _ _ _ _ _ _ _ _ _ _ _ G E.functor hPres
    (U.sheafOfModulesEquivOverUnit X.ringCatSheaf).symm
  exact SheafOfModules.GeneratingSections.equivOfIso
    ((Scheme.Modules.overFunctorEquiv U).app M) H

theorem fromOver_finite {X : Scheme.{u}} (M : X.Modules) (U : X.Opens)
    (G : (M.over U).GeneratingSections) [hG : G.IsFiniteType] :
    (fromOver M U G).IsFiniteType := by
  constructor
  exact hG.finite

def toOver {X : Scheme.{u}} (M : X.Modules) (U : X.Opens)
    (G : (M.restrict U.ι).GeneratingSections) : (M.over U).GeneratingSections := by
  let E := Scheme.Modules.overEquiv U
  let hPres : PreservesColimitsOfSize.{u, u} E.inverse :=
    E.symm.toAdjunction.leftAdjoint_preservesColimits
  let H := @SheafOfModules.GeneratingSections.map _ _ _ _ _ _ _ _ _ _ _ _ _ G E.inverse hPres
    (U.sheafOfModulesEquivOverInverseUnit X.ringCatSheaf).symm
  let e := (E.inverse.mapIso ((Scheme.Modules.overFunctorEquiv U).app M)).symm ≪≫
    (E.unitIso.app (M.over U)).symm
  exact SheafOfModules.GeneratingSections.equivOfIso e H

theorem toOver_finite {X : Scheme.{u}} (M : X.Modules) (U : X.Opens)
    (G : (M.restrict U.ι).GeneratingSections) [hG : G.IsFiniteType] :
    (toOver M U G).IsFiniteType := by
  constructor
  exact hG.finite

theorem finiteType_of_open_generators {X : Scheme.{u}} (M : X.Modules) {ι : Type u}
    (U : ι → X.Opens) (hU : IsOpenCover U)
    (G : ∀ i, (M.restrict (U i).ι).GeneratingSections)
    (hG : ∀ i, (G i).IsFiniteType) : M.IsFiniteType := by
  let q : M.LocalGeneratorsData :=
    { I := ι
      X := U
      coversTop := (Opens.coversTop_iff X U).mpr hU
      generators i := toOver M (U i) (G i) }
  refine { exists_localGeneratorsData := ?_ }
  refine ⟨q, ?_⟩
  constructor
  intro i
  exact ⟨(hG i).finite⟩

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Independent.OpenGenerators
