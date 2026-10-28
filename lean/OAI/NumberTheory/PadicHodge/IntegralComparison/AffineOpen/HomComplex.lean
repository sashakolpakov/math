import OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.ProjectiveResolutionTerms
import OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.ModuleExactSections

/-! # Hom Complex -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.AffineOpen.HomComplex

noncomputable section

/-! The genuine internal-Hom complex on an affine open is the ordinary
Hom complex of the affine section modules, with its actual differentials. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

set_option backward.isDefEq.respectTransparency false

universe u

variable {X : Scheme.{u}} (U : X.Opens) (hU : IsAffineOpen U) (N : X.Modules)

def sectionHom : X.Modulesᵒᵖ ⥤ AddCommGrpCat.{u} :=
  SchemeInternalHom.functor N ⋙ Affine.ModuleExactSections.sections U ⋙
    forget₂ (ModuleCat Γ(X, U)) AddCommGrpCat

def algebraicHom : X.Modulesᵒᵖ ⥤ AddCommGrpCat.{u} :=
  (InternalHom.sections U hU).op ⋙
    preadditiveYoneda.obj ((InternalHom.sections U hU).obj N)

instance sectionHom_additive : (sectionHom U N).Additive := by
  unfold sectionHom
  infer_instance

instance algebraicHom_additive : (algebraicHom U hU N).Additive := by
  unfold algebraicHom
  infer_instance

def complexIso {ι : Type*} (c : ComplexShape ι) (K : HomologicalComplex X.Modulesᵒᵖ c)
    [∀ n, (K.X n).unop.IsQuasicoherent] :
    (((sectionHom U N).mapHomologicalComplex c).obj K) ≅
      (((algebraicHom U hU N).mapHomologicalComplex c).obj K) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => (InternalHom.equiv U hU (K.X n).unop N).toAddCommGrpIso) (by
      intro i j hij
      ext q
      exact (InternalHom.precomp U hU (K.X j).unop N (K.d i j).unop q).symm)

def homologyIso {ι : Type*} (c : ComplexShape ι) (K : HomologicalComplex X.Modulesᵒᵖ c)
    [∀ n, (K.X n).unop.IsQuasicoherent] (n : ι) :
    ((((sectionHom U N).mapHomologicalComplex c).obj K).homology n) ≅
      ((((algebraicHom U hU N).mapHomologicalComplex c).obj K).homology n) :=
  HomologicalComplex.homologyMapIso (complexIso U hU N c K) n

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.AffineOpen.HomComplex
