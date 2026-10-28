import OAI.AlgebraicGeometry.Quotients.FiniteDescent.BaseScalar
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.FormalProducts
import OAI.AlgebraicGeometry.SheafCohomology.Projective.OrderedBaseCech
import Mathlib.Algebra.Homology.Additive

/-! # Cech Scalar Coface -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.CechScalarCoface

noncomputable section

/-! Restricting coefficients identifies the two ordered Cech complexes of a
composite structural morphism. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
open _root_.AlgebraicGeometry.Scheme.Modules

universe u

namespace Construction.CechScalarRestriction

variable {X T S : Scheme.{u}} (f : X ⟶ T) (g : T ⟶ S) (M : X.Modules)

def evaluationIso :
    (FormalCoproduct.evalOp.{u} X.Opens (ModuleCat.{u} Γ(S, ⊤))).obj
        (SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf (f ≫ g) M) ≅
      (FormalCoproduct.evalOp.{u} X.Opens (ModuleCat.{u} Γ(T, ⊤))).obj (SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf f M) ⋙
        ModuleCat.restrictScalars g.appTop.hom :=
  (FormalCoproduct.evalOp.{u} X.Opens (ModuleCat.{u} Γ(S, ⊤))).mapIso
      (BaseScalar.Construction.BaseScalarRestriction.presheafIso f g M) ≪≫
    (FormalProducts.Construction.FormalProductsFunctor.evalIso (ModuleCat.restrictScalars g.appTop.hom)
      (SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf f M)).symm

variable {ι : Type u} [LinearOrder ι] (U : ι → X.Opens)

def objectIso (q : ℕ) : SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.orderedBaseCechObject (f ≫ g) M U q ≅
    (ModuleCat.restrictScalars g.appTop.hom).obj (SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.orderedBaseCechObject f M U q) :=
  (evaluationIso f g M).app (op (SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.orderedCechFormalObject U q))

theorem coface (q : ℕ) (k : Fin (q + 2)) :
    SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.orderedBaseCechCoface (f ≫ g) M U q k ≫ (objectIso f g M U (q + 1)).hom =
      (objectIso f g M U q).hom ≫ (ModuleCat.restrictScalars g.appTop.hom).map
        (SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.orderedBaseCechCoface f M U q k) :=
  (evaluationIso f g M).hom.naturality (SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.orderedCechFace U q k).op

theorem differential (q : ℕ) :
    SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.orderedBaseCechDifferential (f ≫ g) M U q ≫ (objectIso f g M U (q + 1)).hom =
      (objectIso f g M U q).hom ≫ (ModuleCat.restrictScalars g.appTop.hom).map
        (SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.orderedBaseCechDifferential f M U q) := by
  simp only [SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.orderedBaseCechDifferential, Preadditive.sum_comp, Preadditive.comp_sum,
    Functor.map_sum, Functor.map_zsmul, Preadditive.zsmul_comp, Preadditive.comp_zsmul]
  apply Finset.sum_congr rfl
  intro k _
  rw [coface]

def complexIso : SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.orderedBaseCechComplex (f ≫ g) M U ≅
    ((ModuleCat.restrictScalars g.appTop.hom).mapHomologicalComplex (ComplexShape.up ℕ)).obj
      (SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.orderedBaseCechComplex f M U) :=
  HomologicalComplex.Hom.isoOfComponents (objectIso f g M U) (by
    intro i j hij
    change i + 1 = j at hij
    subst j
    change (objectIso f g M U i).hom ≫
      (ModuleCat.restrictScalars g.appTop.hom).map ((SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.orderedBaseCechComplex f M U).d i (i + 1)) =
        (SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.orderedBaseCechComplex (f ≫ g) M U).d i (i + 1) ≫ (objectIso f g M U (i + 1)).hom
    rw [SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.orderedBaseCechComplex_d, SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.orderedBaseCechComplex_d]
    exact (differential f g M U i).symm)

end Construction.CechScalarRestriction

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.CechScalarCoface
