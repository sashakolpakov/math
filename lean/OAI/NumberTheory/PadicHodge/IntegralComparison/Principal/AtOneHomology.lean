import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.ModuleHomology
import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.AtOne
import OAI.NumberTheory.PadicHodge.IntegralComparison.ComposedHomologyNaturality
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory

/-! # At One Homology -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.AtOneHomology

noncomputable section

/-! The principal-section homology comparison at the unit open is
the original affine-section homology comparison. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite _root_.HomologicalComplex

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable {X : Scheme.{u}} (U : X.Opens) (hU : IsAffineOpen U)

theorem preservesRight (S : ShortComplex X.Modules)
    [S.X₁.IsQuasicoherent] [S.X₂.IsQuasicoherent] :
    (ModuleFunctor.functor U hU).PreservesRightHomologyOf S := by
  let h := ShortComplex.RightHomologyData.ofHasCokernelOfHasKernel S
  let : h.IsPreservedBy (ModuleFunctor.functor U hU) :=
    { f := ModuleHomology.preservesCokernel U hU S.f
      g' := ModuleHomology.preservesKernel U hU h.g' }
  exact Functor.PreservesRightHomologyOf.mk' (ModuleFunctor.functor U hU) h

variable (K : CochainComplex X.Modules ℕ) [∀ q, (K.X q).IsQuasicoherent] (c : ℕ)

def affineIso :
    (((Affine.ModuleExactSections.sections U).mapHomologicalComplex (.up ℕ)).obj K).homology c ≅
      (Affine.ModuleExactSections.sections U).obj (K.homology c) := by
  let : (K.sc c).X₁.IsQuasicoherent := inferInstanceAs (K.X ((ComplexShape.up ℕ).prev c)).IsQuasicoherent
  let : (K.sc c).X₂.IsQuasicoherent := inferInstanceAs (K.X c).IsQuasicoherent
  let : (K.sc c).X₃.IsQuasicoherent := inferInstanceAs (K.X ((ComplexShape.up ℕ).next c)).IsQuasicoherent
  exact Affine.ModuleHomology.iso U hU (K.sc c)

local notation "F" => OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.ModuleFunctor.functor U hU

abbrev evaluation := (CategoryTheory.evaluation (SectionPresheaf.Index U)ᵒᵖ
  (ModuleCat Γ(X, U))).obj (op (AtOne.object U))

local notation "E" => OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.AtOneHomology.evaluation U

def evaluationIso :=
  (((((F).mapHomologicalComplex (.up ℕ)).obj K).sc c).mapHomologyIso E)

theorem square :
    ((AtOne.iso U hU).app (K.homology c)).hom ≫
        (ModuleHomology.complexIso U hU K c).inv.app (op (AtOne.object U)) =
      (affineIso U hU K c).inv ≫
        homologyMap (((NatIso.mapHomologicalComplex (AtOne.iso U hU) (.up ℕ)).app K).hom) c ≫
          (evaluationIso U hU K c).hom := by
  let : (K.sc c).X₁.IsQuasicoherent := inferInstanceAs (K.X ((ComplexShape.up ℕ).prev c)).IsQuasicoherent
  let : (K.sc c).X₂.IsQuasicoherent := inferInstanceAs (K.X c).IsQuasicoherent
  let : (K.sc c).X₃.IsQuasicoherent := inferInstanceAs (K.X ((ComplexShape.up ℕ).next c)).IsQuasicoherent
  let : (F).PreservesLeftHomologyOf (K.sc c) := ModuleHomology.preservesLeft U hU (K.sc c)
  let : (F).PreservesRightHomologyOf (K.sc c) := preservesRight U hU (K.sc c)
  let : (Affine.ModuleExactSections.sections U).PreservesLeftHomologyOf (K.sc c) :=
    Affine.ModuleHomology.preservesLeft U hU (K.sc c)
  let : (Affine.ModuleExactSections.sections U).PreservesRightHomologyOf (K.sc c) :=
    Affine.ModuleHomology.preservesRight U hU (K.sc c)
  exact ComposedHomologyNaturality.square F E (Affine.ModuleExactSections.sections U)
    (AtOne.iso U hU).hom (K.sc c)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.AtOneHomology
