import OAI.AlgebraicGeometry.Comparison.Betti.Open.UnitFrame

/-! # Frame Section Restriction -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Open.FrameSectionRestriction.Dolbeault

noncomputable section

/-! A single actual open frame gives compatible section coordinates on every
smaller open, using the original presheaf restriction maps. -/

open _root_.CategoryTheory _root_.TopologicalSpace Opposite

variable {M : TopCat.{0}} (R : TopCat.Sheaf RingCat.{0} M)
  (F : SheafOfModules.{0} R) (U : Opens M)
  (e : F.over U ≅ SheafOfModules.unit.{0} (R.over U))

def openFrameSubsectionIso (V : Opens M) (hVU : V ≤ U) :
    F.val.obj (op V) ≅ (SheafOfModules.unit.{0} R).val.obj (op V) :=
  (SheafOfModules.evaluation (R := R.over U) (op (Over.mk (homOfLE hVU)))).mapIso e

def openFrameSubsectionEquiv (V : Opens M) (hVU : V ≤ U) :
    F.val.obj (op V) ≃ₗ[R.obj.obj (op V)] R.obj.obj (op V) :=
  (openFrameSubsectionIso R F U e V hVU).toLinearEquiv

theorem openFrameSubsectionEquiv_apply (V : Opens M) (hVU : V ≤ U)
    (a : F.val.obj (op V)) :
    openFrameSubsectionEquiv R F U e V hVU a =
      e.hom.val.app (op (Over.mk (homOfLE hVU))) a := rfl

theorem openFrameSubsectionEquiv_restrict {V W : Opens M} (hVW : V ≤ W) (hWU : W ≤ U)
    (a : F.val.obj (op W)) :
    openFrameSubsectionEquiv R F U e V (hVW.trans hWU) (F.val.map (homOfLE hVW).op a) =
      R.obj.map (homOfLE hVW).op (openFrameSubsectionEquiv R F U e W hWU a) :=
  PresheafOfModules.naturality_apply e.hom.val
    (Over.homMk (homOfLE hVW) (by apply Subsingleton.elim) :
      Over.mk (homOfLE (hVW.trans hWU)) ⟶ Over.mk (homOfLE hWU)).op a

theorem openFrameSubsectionEquiv_self :
    openFrameSubsectionEquiv R F U e U le_rfl = UnitFrame.Dolbeault.openUnitFrameSectionEquiv R F U e := rfl

end

end OAI.AlgebraicGeometry.Comparison.Betti.Open.FrameSectionRestriction.Dolbeault
