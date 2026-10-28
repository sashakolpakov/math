import OAI.AlgebraicGeometry.Divisors.LineBundles.Module.OpenPullbackSections
import OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.PullbackIso

/-! # Pullback Unit Sections -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Module.PullbackUnitSections.BundleCycles

noncomputable section

/-! # LineBundleCycles: the actual pullback unit isomorphism sends pulled-back section coordinates to scalar pullback -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable {X Y : Scheme.{0}} (f : X ⟶ Y)

theorem modulePullbackUnitIso_section (U : Y.Opens) (r : Γ(Y, U)) :
    (LineBundle.OpenRestriction.Cycles.modulePullbackUnitIso f).hom.app (f ⁻¹ᵁ U)
      (OpenPullbackSections.BundleCycles.moduleSectionPullbackOnOpen f (DivisorClass.Chern.Line.Bundles.Construction.structureModule Y) U r) = f.app U r := by
  have : (SheafOfModules.pushforward f.toRingCatSheafHom).IsRightAdjoint :=
    inferInstanceAs ((Scheme.Modules.pushforward f).IsRightAdjoint)
  have H := SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit f.toRingCatSheafHom
  rw [Adjunction.homEquiv_unit] at H
  exact congrArg (fun k => k.val.app (.op U) r) H

theorem lineBundlePullbackGlobalTrivialization_section {L : LineBundles.Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle Y}
    (e : L.sheaf ≅ DivisorClass.Chern.Line.Bundles.Construction.structureModule Y) (U : Y.Opens) (s : Γ(L.sheaf, U)) :
    (LineBundle.PullbackIso.Cycles.lineBundlePullbackGlobalTrivialization e f).hom.app (f ⁻¹ᵁ U)
      (OpenPullbackSections.BundleCycles.moduleSectionPullbackOnOpen f L.sheaf U s) = f.app U (e.hom.app U s) := by
  change (LineBundle.OpenRestriction.Cycles.modulePullbackUnitIso f).hom.app (f ⁻¹ᵁ U)
    (((Scheme.Modules.pullback f).map e.hom).app (f ⁻¹ᵁ U)
      (OpenPullbackSections.BundleCycles.moduleSectionPullbackOnOpen f L.sheaf U s)) = _
  rw [OpenPullbackSections.BundleCycles.moduleSectionPullbackOnOpen_naturality]
  exact modulePullbackUnitIso_section f U (e.hom.app U s)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Module.PullbackUnitSections.BundleCycles
