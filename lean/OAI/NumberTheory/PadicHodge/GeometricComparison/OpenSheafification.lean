import OAI.AlgebraicGeometry.Crystalline.Cohomology.Cech.Cover

/-! # Open Sheafification -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.OpenSheafification.OpenSheafificationUnit

noncomputable section

/-! The canonical sheafification unit on an open image is computed by the actual open restriction. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

variable (R : Type) [CommRing R] {X Y : Scheme.{0}} (f : Y ⟶ X) [IsOpenImmersion f]
  (P : X.Opensᵒᵖ ⥤ ModuleCat.{0} R) (U : Y.Opens)

theorem isIso_on_image
    (hU : IsIso ((toSheafify (Opens.grothendieckTopology Y) (f.opensFunctor.op ⋙ P)).app (op U))) :
    IsIso ((toSheafify (Opens.grothendieckTopology X) P).app (op (f ''ᵁ U))) := by
  have : IsIso ((toSheafify (Opens.grothendieckTopology Y) (f.opensFunctor.op ⋙ P)).app (op U)) := hU
  let e := (AlgebraicGeometry.Crystalline.Cohomology.Cech.Cover.CechRestriction.sheafificationIso R f).app P
  have he : IsIso (e.hom.hom.app (op U)) :=
    (((sheafToPresheaf (Opens.grothendieckTopology Y) (ModuleCat.{0} R)).mapIso e).app (op U)).isIso_hom
  have hw := congrArg (fun a => a.app (op U))
    (f.opensFunctor.toSheafify_pullbackSheafificationCompatibility (ModuleCat.{0} R)
      (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X) P)
  have hi : IsIso (((toSheafify (Opens.grothendieckTopology Y) (f.opensFunctor.op ⋙ P)).app (op U)) ≫
      e.hom.hom.app (op U)) := IsIso.comp_isIso' hU he
  exact hw ▸ hi

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.OpenSheafification.OpenSheafificationUnit
