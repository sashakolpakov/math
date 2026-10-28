import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ModuleHomOf
import OAI.AlgebraicGeometry.SheafCohomology.Projective.OverGenerator
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles
import Mathlib.Topology.Sheaves.LocallySurjective

/-! # Module Local Unit Lifts -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ModuleLocalUnitLifts

noncomputable section

/-! Epimorphisms onto the structure module admit actual local sections
lifting one, and those sections give local splitting maps. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open OAI.AlgebraicGeometry.SheafCohomology.Projective.OverGenerator

theorem module_epi_local_lift {X : Scheme.{0}} {M N : X.Modules} (f : M ⟶ N) [Epi f]
    (U : X.Opens) (z : Γ(N, U)) (x : X) (hx : x ∈ U) :
    ∃ (W : X.Opens) (hW : W ≤ U), x ∈ W ∧ ∃ w : Γ(M, W),
      f.app W w = N.presheaf.map (homOfLE hW).op z := by
  let q : (⟨M.presheaf, M.isSheaf⟩ : TopCat.Sheaf AddCommGrpCat.{0} X) ⟶
      (⟨N.presheaf, N.isSheaf⟩ : TopCat.Sheaf AddCommGrpCat.{0} X) := ⟨f.mapPresheaf⟩
  have hqEpi : Epi q := ModuleHomOf.moduleSheaf_toSheaf_epi f
  have hq := (TopCat.Presheaf.isLocallySurjective_iff q.hom).mp
    ((TopCat.Sheaf.isLocallySurjective_iff_epi q).mpr hqEpi)
  obtain ⟨W, hW, ⟨w, hw⟩, hxW⟩ := hq U z x hx
  exact ⟨W, hW, hxW, w, hw⟩

theorem module_epi_unit_local_lift {X : Scheme.{0}} {M : X.Modules}
    (p : M ⟶ HilbertConstruction.Line.Bundles.structureModule X) [Epi p] (x : X) :
    ∃ U : X.Opens, x ∈ U ∧ ∃ z : Γ(M, U), p.app U z = (1 : Γ(X, U)) := by
  obtain ⟨U, hU, hx, z, hz⟩ := module_epi_local_lift p ⊤ (1 : Γ(X, ⊤)) x (by trivial)
  refine ⟨U, hx, z, ?_⟩
  change p.app U z = X.presheaf.map (homOfLE hU).op (1 : Γ(X, ⊤)) at hz
  have h1 : X.presheaf.map (homOfLE hU).op (1 : Γ(X, ⊤)) = (1 : Γ(X, U)) :=
    (X.presheaf.map (homOfLE hU).op).hom.map_one
  exact hz.trans h1

theorem overUnitGenerator_one {X : Scheme.{0}} (U : X.Opens) :
    SheafCohomology.Projective.OverGenerator.overGeneratorHom (HilbertConstruction.Line.Bundles.structureModule X) U (1 : Γ(X, U)) =
      𝟙 (SheafOfModules.unit (X.ringCatSheaf.over U)) := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro W
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  change (show Γ(X, W.unop.left) from a) * X.presheaf.map W.unop.hom.op (1 : Γ(X, U)) = a
  rw [map_one, mul_one]

theorem local_lift_splits_over {X : Scheme.{0}} {M : X.Modules}
    (p : M ⟶ HilbertConstruction.Line.Bundles.structureModule X) (U : X.Opens) (z : Γ(M, U))
    (hz : p.app U z = (1 : Γ(X, U))) :
    SheafCohomology.Projective.OverGenerator.overGeneratorHom M U z ≫ p.over U = 𝟙 _ := by
  rw [SheafCohomology.Projective.OverGenerator.overGeneratorHom_comp]
  exact (congrArg (SheafCohomology.Projective.OverGenerator.overGeneratorHom (HilbertConstruction.Line.Bundles.structureModule X) U) hz).trans (overUnitGenerator_one U)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ModuleLocalUnitLifts
