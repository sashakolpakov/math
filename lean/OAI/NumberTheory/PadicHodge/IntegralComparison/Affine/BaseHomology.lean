import OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.ModuleHomology
import OAI.NumberTheory.PadicHodge.IntegralComparison.HomologyPreservationCompose
import OAI.NumberTheory.PadicHodge.IntegralComparison.AlgebraSheafScalars
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact

/-! # Base Homology -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.BaseHomology

noncomputable section

/-! Affine homology comparisons over the original base ring, natural under restriction. -/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry Opposite

universe u

variable (k : Type u) [CommRing k] (X : Over (Spec (CommRingCat.of k)))

def coefficientMap (U : X.left.Opens) : k →+* Γ(X.left, U) :=
  algebraMap k ((AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebras k X).obj (op U))

abbrev coefficients (U : X.left.Opens) : ModuleCat.{u} Γ(X.left, U) ⥤ ModuleCat.{u} k :=
  ModuleCat.restrictScalars (coefficientMap k X U)

instance coefficients_additive (U : X.left.Opens) : (coefficients k X U).Additive where
  map_add := rfl

instance coefficients_preservesFiniteLimits (U : X.left.Opens) :
    PreservesFiniteLimits (coefficients k X U) where
  preservesFiniteLimits J _ _ := by
    dsimp [coefficients]
    infer_instance

instance coefficients_preservesFiniteColimits (U : X.left.Opens) :
    PreservesFiniteColimits (coefficients k X U) where
  preservesFiniteColimits J _ _ := by
    dsimp [coefficients]
    infer_instance

abbrev sections (U : X.left.Opens) : X.left.Modules ⥤ ModuleCat.{u} k :=
  ModuleExactSections.sections U ⋙ coefficients k X U

instance additive (U : X.left.Opens) : (sections k X U).Additive := by infer_instance

instance preservesFiniteLimits (U : X.left.Opens) : PreservesFiniteLimits (sections k X U) := by
  infer_instance

def restriction {U V : X.left.Opens} (h : V ≤ U) : sections k X U ⟶ sections k X V where
  app M := ((AlgebraSheafScalars.functor k X).obj M).obj.map (homOfLE h).op
  naturality _ _ f := ((AlgebraSheafScalars.functor k X).map f).hom.naturality (homOfLE h).op |>.symm

variable (U : X.left.Opens) (hU : IsAffineOpen U) (S : ShortComplex X.left.Modules)
  [S.X₁.IsQuasicoherent] [S.X₂.IsQuasicoherent] [S.X₃.IsQuasicoherent]

include hU

theorem preservesLeft : (sections k X U).PreservesLeftHomologyOf S := by
  have := ModuleHomology.preservesLeft U hU S
  exact HomologyPreservationCompose.left (ModuleExactSections.sections U) (coefficients k X U) S

omit [S.X₃.IsQuasicoherent] in
theorem preservesRight : (sections k X U).PreservesRightHomologyOf S := by
  have := ModuleHomology.preservesRight U hU S
  exact HomologyPreservationCompose.right (ModuleExactSections.sections U) (coefficients k X U) S

def iso : (S.map (sections k X U)).homology ≅ (sections k X U).obj S.homology := by
  have := preservesLeft k X U hU S
  exact S.mapHomologyIso (sections k X U)

theorem restriction_naturality (V : X.left.Opens) (hV : IsAffineOpen V) (h : V ≤ U) :
    ShortComplex.homologyMap (S.mapNatTrans (restriction k X h)) ≫ (iso k X V hV S).hom =
      (iso k X U hU S).hom ≫ (restriction k X h).app S.homology := by
  have := preservesLeft k X U hU S
  have := preservesRight k X U hU S
  have := preservesLeft k X V hV S
  have := preservesRight k X V hV S
  change ShortComplex.homologyMap (S.mapNatTrans (restriction k X h)) ≫
    (S.mapHomologyIso (sections k X V)).hom =
      (S.mapHomologyIso (sections k X U)).hom ≫ (restriction k X h).app S.homology
  rw [ShortComplex.homologyMap_mapNatTrans]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.BaseHomology
