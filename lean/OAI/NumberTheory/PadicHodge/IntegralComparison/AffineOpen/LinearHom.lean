import OAI.NumberTheory.PadicHodge.IntegralComparison.InternalHomOpenRestriction
import OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.ChartSections

/-! # Linear Hom -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.AffineOpen.LinearHom

noncomputable section

/-! The affine-open internal-Hom comparison as a natural map of modules.
Its source retains the literal section-module structure on the open. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

variable {X : Scheme.{u}} (U : X.Opens) (hU : IsAffineOpen U)

def fromSpecSectionsIso : Affine.ModuleExactSections.sections U ≅
    Scheme.Modules.restrictFunctor hU.fromSpec ⋙ Affine.InternalHom.sections :=
  NatIso.ofComponents (Affine.ChartSections.fromSpecIso U hU) (by
    intro M N a
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact (PresheafOfModules.naturality_apply a.val
      (eqToHom (Affine.ChartSections.image_top U hU)).op x).symm)

def sectionsIso : Affine.ModuleExactSections.sections U ≅
    InternalHom.sections U hU :=
  fromSpecSectionsIso U hU ≪≫
    Functor.isoWhiskerRight (Scheme.Modules.restrictFunctorComp hU.isoSpec.inv U.ι)
      Affine.InternalHom.sections

variable (N : X.Modules)

def chartHomIso (M : X.Modules) :
    (InternalHom.chartFunctor U hU).obj (ArithmeticGeometry.OrdinaryLocus.Openness.SheafHomModule.Construction.sheafHomModule M N) ≅
      ArithmeticGeometry.OrdinaryLocus.Openness.SheafHomModule.Construction.sheafHomModule
        ((InternalHom.chartFunctor U hU).obj M)
        ((InternalHom.chartFunctor U hU).obj N) :=
  (Scheme.Modules.restrictFunctor hU.isoSpec.inv).mapIso
    (InternalHomOpenRestriction.iso U.ι M N) ≪≫
      InternalHomOpenRestriction.iso hU.isoSpec.inv (M.restrict U.ι) (N.restrict U.ι)

def chartHomFunctorIso :
    SchemeInternalHom.functor N ⋙ InternalHom.chartFunctor U hU ≅
      (InternalHom.chartFunctor U hU).op ⋙
        SchemeInternalHom.functor ((InternalHom.chartFunctor U hU).obj N) :=
  NatIso.ofComponents (fun M => chartHomIso U hU N M.unop) (by
    intro M P a
    change (Scheme.Modules.restrictFunctor hU.isoSpec.inv).map
        ((Scheme.Modules.restrictFunctor U.ι).map (ArithmeticGeometry.OrdinaryLocus.Openness.SheafHomFunctoriality.Construction.sheafHomMap a.unop (𝟙 N))) ≫
        (Scheme.Modules.restrictFunctor hU.isoSpec.inv).map
          (InternalHomOpenRestriction.iso U.ι P.unop N).hom ≫
        (InternalHomOpenRestriction.iso hU.isoSpec.inv (P.unop.restrict U.ι)
          (N.restrict U.ι)).hom = _
    rw [← Category.assoc, ← CategoryTheory.Functor.map_comp,
      InternalHomOpenRestriction.precomp, CategoryTheory.Functor.map_comp, Category.assoc,
      InternalHomOpenRestriction.precomp]
    rfl)

def sectionHom : X.Modulesᵒᵖ ⥤ ModuleCat Γ(X, U) :=
  SchemeInternalHom.functor N ⋙ Affine.ModuleExactSections.sections U

def algebraicHom : X.Modulesᵒᵖ ⥤ ModuleCat Γ(X, U) :=
  (InternalHom.sections U hU).op ⋙
    (linearYoneda Γ(X, U) (ModuleCat Γ(X, U))).obj
      ((InternalHom.sections U hU).obj N)

instance sectionHom_additive : (sectionHom U N).Additive := by
  unfold sectionHom
  infer_instance

instance algebraicHom_additive : (algebraicHom U hU N).Additive := by
  let : (InternalHom.sections U hU).Additive := { map_add := rfl }
  unfold algebraicHom
  infer_instance

def comparison : sectionHom U N ⟶ algebraicHom U hU N :=
  Functor.whiskerLeft (SchemeInternalHom.functor N) (sectionsIso U hU).hom ≫
    Functor.whiskerRight (chartHomFunctorIso U hU N).hom Affine.InternalHom.sections ≫
      Functor.whiskerLeft (InternalHom.chartFunctor U hU).op
        (Affine.InternalHomComplex.comparison
          ((InternalHom.chartFunctor U hU).obj N))

theorem comparison_isIso (M : X.Modulesᵒᵖ) [M.unop.IsQuasicoherent] :
    IsIso ((comparison U hU N).app M) := by
  let : ((InternalHom.chartFunctor U hU).obj M.unop).IsQuasicoherent :=
    InternalHom.chart_quasicoherent U hU M.unop
  let := Affine.InternalHomComplex.comparison_isIso
    ((InternalHom.chartFunctor U hU).obj N)
    (op ((InternalHom.chartFunctor U hU).obj M.unop))
  change IsIso ((sectionsIso U hU).hom.app _ ≫
    Affine.InternalHom.sections.map ((chartHomFunctorIso U hU N).hom.app M) ≫
      (Affine.InternalHomComplex.comparison
        ((InternalHom.chartFunctor U hU).obj N)).app
          (op ((InternalHom.chartFunctor U hU).obj M.unop)))
  infer_instance

def complexMap {ι : Type*} (c : ComplexShape ι)
    (K : HomologicalComplex X.Modulesᵒᵖ c) :
    ((sectionHom U N).mapHomologicalComplex c).obj K ⟶
      ((algebraicHom U hU N).mapHomologicalComplex c).obj K :=
  ((comparison U hU N).mapHomologicalComplex c).app K

theorem complexMap_isIso {ι : Type*} (c : ComplexShape ι)
    (K : HomologicalComplex X.Modulesᵒᵖ c)
    [∀ i, (K.X i).unop.IsQuasicoherent] : IsIso (complexMap U hU N c K) := by
  let (i : ι) : IsIso ((complexMap U hU N c K).f i) := comparison_isIso U hU N (K.X i)
  exact HomologicalComplex.Hom.isIso_of_components _

def complexIso {ι : Type*} (c : ComplexShape ι)
    (K : HomologicalComplex X.Modulesᵒᵖ c)
    [∀ i, (K.X i).unop.IsQuasicoherent] :
    ((sectionHom U N).mapHomologicalComplex c).obj K ≅
      ((algebraicHom U hU N).mapHomologicalComplex c).obj K := by
  letI := complexMap_isIso U hU N c K
  exact asIso (complexMap U hU N c K)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.AffineOpen.LinearHom
