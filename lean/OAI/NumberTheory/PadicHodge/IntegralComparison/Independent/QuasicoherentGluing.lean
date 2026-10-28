import Mathlib.AlgebraicGeometry.Modules.Tilde

/-! # Quasicoherent Gluing -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Independent.QuasicoherentGluing

noncomputable section

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry _root_.TopologicalSpace

universe u

variable {X : Scheme.{u}} (M : X.Modules)

def presentationOver (U : X.Opens) (P : (M.restrict U.ι).Presentation) :
    (M.over U).Presentation := by
  let E := Scheme.Modules.overEquiv U
  let hPres : PreservesColimitsOfSize.{u, u} E.inverse :=
    E.symm.toAdjunction.leftAdjoint_preservesColimits
  let Q := @SheafOfModules.Presentation.map
    _ _ _ _ _ _ _ _ _ _ _ _ _ P E.inverse hPres
      (U.sheafOfModulesEquivOverInverseUnit X.ringCatSheaf).symm
  let e : E.inverse.obj (M.restrict U.ι) ≅ M.over U :=
    (E.inverse.mapIso ((Scheme.Modules.overFunctorEquiv U).app M)).symm ≪≫
      (E.unitIso.app (M.over U)).symm
  exact Q.ofIsIso e.hom

theorem of_open_presentations {ι : Type u} (U : ι → X.Opens) (hU : IsOpenCover U)
    (P : ∀ i, (M.restrict (U i).ι).Presentation) : M.IsQuasicoherent := by
  let q : M.QuasicoherentData :=
    { I := ι
      X := U
      coversTop := (Opens.coversTop_iff X U).mpr hU
      presentation := fun i => presentationOver M (U i) (P i) }
  exact q.isQuasicoherent

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Independent.QuasicoherentGluing
