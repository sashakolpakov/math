import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.OrderedCechCoverCohomology
import OAI.AlgebraicGeometry.SheafCohomology.Projective.OrderedBaseCechFunctor

/-! # Ordered Cech Naturality -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.OrderedCechNaturality.Construction

noncomputable section

/-! Naturality of projection from all Cech tuples to ordered tuples. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace
open _root_.AlgebraicGeometry.Scheme.Modules

universe u

variable {X S : Scheme.{u}} (π : X ⟶ S) {M N : X.Modules} (q : M ⟶ N)
variable {ι : Type u} [LinearOrder ι] (U : ι → X.Opens)

theorem baseCechToOrdered_naturality :
    (AlgebraicGeometry.SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechComplexFunctor π U).map q ≫ AlgebraicGeometry.SheafCohomology.Projective.OrderedBaseCechComparison.Scheme.Modules.baseCechToOrdered π N U =
      AlgebraicGeometry.SheafCohomology.Projective.OrderedBaseCechComparison.Scheme.Modules.baseCechToOrdered π M U ≫ (AlgebraicGeometry.SheafCohomology.Projective.OrderedBaseCechFunctor.Scheme.Modules.orderedBaseCechComplexFunctor π U).map q := by
  apply HomologicalComplex.hom_ext
  intro n
  let E : (X.Opensᵒᵖ ⥤ ModuleCat.{u} Γ(S, ⊤)) ⥤
      ((FormalCoproduct.{u} X.Opens)ᵒᵖ ⥤ ModuleCat.{u} Γ(S, ⊤)) :=
    FormalCoproduct.evalOp X.Opens (ModuleCat.{u} Γ(S, ⊤))
  let α := E.map ((AlgebraicGeometry.SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheafFunctor π).map q)
  exact (α.naturality (AlgebraicGeometry.SheafCohomology.Projective.OrderedBaseCechComparison.Scheme.Modules.orderedCechFormalInclusion U n).op).symm

theorem baseCechOrderedHomologyIso_naturality (n : ℕ) :
    HomologicalComplex.homologyMap ((AlgebraicGeometry.SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechComplexFunctor π U).map q) n ≫
      (AlgebraicGeometry.SheafCohomology.Projective.BaseCechHomotopyEquiv.Scheme.Modules.baseCechOrderedHomologyIso π N U n).hom =
    (AlgebraicGeometry.SheafCohomology.Projective.BaseCechHomotopyEquiv.Scheme.Modules.baseCechOrderedHomologyIso π M U n).hom ≫
      HomologicalComplex.homologyMap ((AlgebraicGeometry.SheafCohomology.Projective.OrderedBaseCechFunctor.Scheme.Modules.orderedBaseCechComplexFunctor π U).map q) n := by
  have h := congrArg (fun a : AlgebraicGeometry.SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechComplex π M U ⟶ AlgebraicGeometry.SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.orderedBaseCechComplex π N U ↦
    HomologicalComplex.homologyMap a n) (baseCechToOrdered_naturality π q U)
  exact (HomologicalComplex.homologyMap_comp ((AlgebraicGeometry.SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechComplexFunctor π U).map q)
    (AlgebraicGeometry.SheafCohomology.Projective.OrderedBaseCechComparison.Scheme.Modules.baseCechToOrdered π N U) n).symm.trans (h.trans
      (HomologicalComplex.homologyMap_comp (AlgebraicGeometry.SheafCohomology.Projective.OrderedBaseCechComparison.Scheme.Modules.baseCechToOrdered π M U)
        ((AlgebraicGeometry.SheafCohomology.Projective.OrderedBaseCechFunctor.Scheme.Modules.orderedBaseCechComplexFunctor π U).map q) n))

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.OrderedCechNaturality.Construction
