import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.ComponentRatios
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coefficient.AlgebraPresheaf
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coefficient.GlobalSectionsFunctor
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.Gluing

/-! # Section Coordinates -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coefficient.SectionCoordinates

noncomputable section

/-! Restricting a global section and taking its coordinate in a local frame is linear over the chosen coefficient ring. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {R : Type u} [CommRing R] {X : Scheme.{u}} {M : X.Modules}

def coefficientFrameCoordinateEquiv (f : R →+* Γ(X, ⊤)) (U : X.Opens)
    (e : Γ(M, U) ≃ₗ[Γ(X, U)] Γ(X, U)) :
    (ModulePresheaf.coefficientModulePresheaf f M).obj (.op U) ≃ₗ[R] AlgebraPresheaf.coefficientAlgebraSections f U where
  toFun := e
  invFun := e.symm
  left_inv := e.left_inv
  right_inv := e.right_inv
  map_add' := e.map_add
  map_smul' r s := e.map_smul (AlgebraPresheaf.coefficientSectionMap f U r) s

def sectionCoordinateLinear (p : X ⟶ Spec (.of R)) (s : Line.Bundles.structureModule X ⟶ M)
    (U : X.Opens) (hU : U ≤ Ample.LineBundles.sectionNonvanishing s) :
    (GlobalSectionsFunctor.schemeGlobalSectionsFunctor p).obj M →ₗ[R] AlgebraPresheaf.coefficientAlgebraSections (ModulePresheaf.schemeCoefficientMap p) U :=
  (coefficientFrameCoordinateEquiv (ModulePresheaf.schemeCoefficientMap p) U (Section.LocalLinearFrames.sectionLocalFrameEquiv s U hU).symm).toLinearMap.comp
    ((ModulePresheaf.schemeModulePresheaf p M).map U.leTop.op).hom

theorem sectionCoordinateLinear_value (p : X ⟶ Spec (.of R)) (s t : Line.Bundles.structureModule X ⟶ M)
    (U : X.Opens) (hU : U ≤ Ample.LineBundles.sectionNonvanishing s) :
    sectionCoordinateLinear p s U hU (Global.Sections.moduleSectionHomEquiv M t) = Section.ComponentRatios.sectionComponentRatio s t U hU := by
  change (Section.LocalLinearFrames.sectionLocalFrameEquiv s U hU).symm
    (M.presheaf.map U.leTop.op (Global.Sections.moduleSectionHomEquiv M t)) = _
  rw [Section.Gluing.moduleSectionHomEquiv_restrict]
  rfl

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coefficient.SectionCoordinates
