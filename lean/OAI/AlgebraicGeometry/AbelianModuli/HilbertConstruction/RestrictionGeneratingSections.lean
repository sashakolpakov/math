/-
Derived from AINTLIB:
  projects/ModularCurves/ModularCurves/ForMathlib/SchemeModuleQuasicoherent.lean
The upstream AINTLIB repository is licensed under Apache 2.0.
This file has been modified.
-/
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.OverGeneratorFiniteness

/-! # Restriction Generating Sections -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.RestrictionGeneratingSections

noncomputable section

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.AlgebraicGeometry.Scheme.Modules

universe u

/-- Generating sections of a restriction give generating sections of the corresponding
over-site module. -/
noncomputable def generatingSectionsOverOfRestrict
    {X : Scheme.{u}} (M : X.Modules) (U : X.Opens)
    (G : (M.restrict U.ι).GeneratingSections) :
    (M.over U).GeneratingSections := by
  let N := M.restrict U.ι
  letI : (overEquiv U).inverse.IsEquivalence := by
    infer_instance
  let hPres : PreservesColimitsOfSize.{u, u} (overEquiv U).inverse := by
    infer_instance
  let G' := @SheafOfModules.GeneratingSections.map
    _ _ _ _ _ _ _ _ _ _ _ _ _ G (overEquiv U).inverse hPres
      (U.sheafOfModulesEquivOverInverseUnit X.ringCatSheaf).symm
  let e : M.over U ≅ (overEquiv U).inverse.obj N :=
    (overEquiv U).unitIso.app (M.over U) ≪≫
      (overEquiv U).inverse.mapIso ((overFunctorEquiv U).app M)
  exact (SheafOfModules.GeneratingSections.equivOfIso e).symm G'

/-- The over-site generating sections induced from finite generating sections of a restriction
are finite. -/
theorem generatingSectionsOverOfRestrict_isFiniteType
    {X : Scheme.{u}} (M : X.Modules) (U : X.Opens)
    (G : (M.restrict U.ι).GeneratingSections) [G.IsFiniteType] :
    (generatingSectionsOverOfRestrict M U G).IsFiniteType where
  finite := by
    change Finite G.I
    exact SheafOfModules.GeneratingSections.IsFiniteType.finite

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.RestrictionGeneratingSections
