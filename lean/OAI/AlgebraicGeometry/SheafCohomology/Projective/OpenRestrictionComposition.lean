import OAI.AlgebraicGeometry.SheafCohomology.Projective.OpenOverCoherence

/-! # Open Restriction Composition -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.OpenRestrictionComposition

noncomputable section

/-! Native restriction along nested open subschemes and its frame comparison. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
universe u

def nestedRestrictionIso {X : Scheme.{u}} {U V : X.Opens} (h : V ≤ U)
    (M : X.Modules) : M.restrict V.ι ≅
      (M.restrict U.ι).restrict (X.homOfLE h) :=
  (Scheme.Modules.restrictFunctorCongr (X.homOfLE_ι h).symm).app M ≪≫
    (Scheme.Modules.restrictFunctorComp (X.homOfLE h) U.ι).app M

def nativeOpenFrame {X : Scheme.{u}} {M : X.Modules} {U V : X.Opens}
    (h : V ≤ U) (e : M.restrict U.ι ≅ Invertible.Scheme.Modules.unitObj U.toScheme) :
    M.restrict V.ι ≅ Invertible.Scheme.Modules.unitObj V.toScheme :=
  nestedRestrictionIso h M ≪≫
    (Scheme.Modules.restrictFunctor (X.homOfLE h)).mapIso e ≪≫
    Scheme.Modules.restrictUnitIso (X.homOfLE h)

theorem nativeOpenFrame_of_over {X : Scheme.{u}} {M : X.Modules}
    {U V : X.Opens} (h : V ≤ U)
    (e : M.over U ≅ _root_.SheafOfModules.unit (X.ringCatSheaf.over U)) :
    nativeOpenFrame h (FrameSections.restrictTrivializationOfOverIso M U e) =
    FrameSections.restrictTrivializationOfOverIso M V
      (Dual.SheafOfModules.restrictOverTrivialization X.ringCatSheaf M U e
        (Over.mk (homOfLE h))) := by
  apply Iso.ext
  have hn := (Scheme.Modules.overMapCompOverEquiv (homOfLE h)).hom.naturality e.hom
  have hc := OpenOverCoherence.overRestriction_comparison h M
  have hu := OpenOverCoherence.overRestriction_unit h
  simp only [Functor.comp_map] at hn
  simp only [nativeOpenFrame, nestedRestrictionIso, FrameSections.restrictTrivializationOfOverIso,
    Dual.SheafOfModules.restrictOverTrivialization, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom, Functor.map_comp, Category.assoc]
  slice_lhs 1 3 => erw [← hc]
  simp only [Category.assoc]
  slice_lhs 3 4 => erw [← hn]
  simp only [Category.assoc]
  erw [hu]
  rfl

theorem nativeOpenFrame_eq_over {X : Scheme.{u}} {M : X.Modules}
    {U V : X.Opens} (h : V ≤ U)
    (e : M.restrict U.ι ≅ Invertible.Scheme.Modules.unitObj U.toScheme) :
    nativeOpenFrame h e = OpenFrames.Scheme.Modules.restrictOpenTrivialization h e := by
  have H := nativeOpenFrame_of_over h
    (Invertible.Scheme.Modules.overTrivializationOfRestrictIso M U e)
  rw [OpenFrames.restrictTrivializationOfOverTrivializationOfRestrictIso] at H
  exact H

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.OpenRestrictionComposition
