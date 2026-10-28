import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.InternalHom
import OAI.NumberTheory.PadicHodge.IntegralComparison.SchemeInternalHom
import OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.ModuleExactSections

/-! # Internal Hom Complex -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.InternalHomComplex

noncomputable section

/-! The original internal-Hom complex on the whole principal-open
diagram is naturally the ordinary Hom complex of its fixed affine
section modules with varying native section coefficients. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.SectionPresheaf
variable {X : Scheme.{u}} (U : X.Opens) (hU : IsAffineOpen U) (N : X.Modules)

def sectionHom : X.Modulesᵒᵖ ⥤ ((SectionPresheaf.Index U)ᵒᵖ ⥤ ModuleCat.{u} Γ(X, U)) :=
  SchemeInternalHom.functor N ⋙ ModuleFunctor.functor U hU

def algebraicHom : X.Modulesᵒᵖ ⥤ ((SectionPresheaf.Index U)ᵒᵖ ⥤ ModuleCat.{u} Γ(X, U)) :=
  (Affine.ModuleExactSections.sections U).op ⋙
    HomCoefficientFunctor.functor Γ(X, U) (SectionPresheaf.modules U hU N)

instance sectionHom_additive : (sectionHom U hU N).Additive := by
  unfold sectionHom
  infer_instance

instance algebraicHom_additive : (algebraicHom U hU N).Additive := by
  unfold algebraicHom
  infer_instance

def iso {ι : Type*} (c : ComplexShape ι) (K : HomologicalComplex X.Modulesᵒᵖ c)
    [∀ n, (K.X n).unop.IsQuasicoherent] :
    (((sectionHom U hU N).mapHomologicalComplex c).obj K) ≅
      (((algebraicHom U hU N).mapHomologicalComplex c).obj K) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => InternalHom.iso U hU (K.X n).unop N) (by
      intro i j hij
      exact (InternalHom.precomp U hU (K.X j).unop N (K.d i j).unop).symm)

theorem naturality {ι : Type*} (c : ComplexShape ι)
    {K L : HomologicalComplex X.Modulesᵒᵖ c}
    [∀ n, (K.X n).unop.IsQuasicoherent] [∀ n, (L.X n).unop.IsQuasicoherent]
    (f : K ⟶ L) :
    ((sectionHom U hU N).mapHomologicalComplex c).map f ≫ (iso U hU N c L).hom =
      (iso U hU N c K).hom ≫ ((algebraicHom U hU N).mapHomologicalComplex c).map f := by
  apply HomologicalComplex.Hom.ext
  funext i
  exact InternalHom.precomp U hU (L.X i).unop N (f.f i).unop

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.InternalHomComplex
