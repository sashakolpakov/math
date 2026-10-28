import OAI.AlgebraicGeometry.Divisors.LineBundles.Module.SectionIso
import OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.FrameComparison

/-! # Global Frame -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.GlobalFrame.Cycles

noncomputable section

/-! # LineBundleCycles: an actual global sheaf trivialization supplies compatible frames on every open -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

def structureModuleFrame (X : Scheme.{0}) (U : X.Opens) :
    Γ(DivisorClass.Chern.Line.Bundles.Construction.structureModule X, U) ≃ₗ[Γ(X, U)] Γ(X, U) where
  toFun r := r
  invFun r := r
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem structureModuleFrame_naturality {X : Scheme.{0}} {U V : X.Opens} (h : U ≤ V)
    (r : Γ(DivisorClass.Chern.Line.Bundles.Construction.structureModule X, V)) :
    structureModuleFrame X U ((DivisorClass.Chern.Line.Bundles.Construction.structureModule X).presheaf.map (homOfLE h).op r) =
      X.presheaf.map (homOfLE h).op (structureModuleFrame X V r) := rfl

variable {X : Scheme.{0}} {L : LineBundles.Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle X} (e : L.sheaf ≅ DivisorClass.Chern.Line.Bundles.Construction.structureModule X)

def lineBundleGlobalFrame (U : X.Opens) : Γ(L.sheaf, U) ≃ₗ[Γ(X, U)] Γ(X, U) :=
  (Module.SectionIso.BundleCycles.moduleSectionIso e U).trans (structureModuleFrame X U)

theorem lineBundleGlobalFrame_naturality {U V : X.Opens} (h : U ≤ V) (m : Γ(L.sheaf, V)) :
    lineBundleGlobalFrame e U (L.sheaf.presheaf.map (homOfLE h).op m) =
      X.presheaf.map (homOfLE h).op (lineBundleGlobalFrame e V m) := by
  change structureModuleFrame X U (Module.SectionIso.BundleCycles.moduleSectionIso e U (L.sheaf.presheaf.map (homOfLE h).op m)) = _
  rw [Module.SectionIso.BundleCycles.moduleSectionIso_naturality, structureModuleFrame_naturality]
  rfl

def lineBundleGlobalFrameTransition (x : X) (W : X.Opens) (hW : W ≤ L.trivializingOpen x) : Γ(X, W)ˣ :=
  FrameComparison.Cycles.LineBundleConstruction.frameTransitionUnit (lineBundleGlobalFrame e W) (L.sectionFrame x W hW)

theorem lineBundleGlobalFrameTransition_restrict (x : X) {V W : X.Opens} (hVW : V ≤ W)
    (hW : W ≤ L.trivializingOpen x) :
    Units.map (X.presheaf.map (homOfLE hVW).op).hom.toMonoidHom (lineBundleGlobalFrameTransition e x W hW) =
      lineBundleGlobalFrameTransition e x V (hVW.trans hW) :=
  FrameComparison.Cycles.LineBundleConstruction.frameTransitionUnit_map (X.presheaf.map (homOfLE hVW).op).hom
    (L.sheaf.presheaf.map (homOfLE hVW).op)
    (lineBundleGlobalFrame e W) (L.sectionFrame x W hW)
    (lineBundleGlobalFrame e V) (L.sectionFrame x V (hVW.trans hW))
    (lineBundleGlobalFrame_naturality e hVW) (L.sectionFrame_naturality x hVW hW)

theorem lineBundleGlobalFrameTransition_cocycle (x y : X) (W : X.Opens)
    (hx : W ≤ L.trivializingOpen x) (hy : W ≤ L.trivializingOpen y) :
    lineBundleGlobalFrameTransition e x W hx * L.ambientTransitionOn x y W hx hy =
      lineBundleGlobalFrameTransition e y W hy :=
  FrameComparison.Cycles.LineBundleConstruction.frameTransitionUnit_cocycle _ _ _

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.GlobalFrame.Cycles
