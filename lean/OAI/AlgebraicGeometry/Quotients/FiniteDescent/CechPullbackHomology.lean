import OAI.AlgebraicGeometry.SheafCohomology.Projective.OrderedBaseCechFunctor
import OAI.AlgebraicGeometry.SheafCohomology.Projective.OrderedBaseCechPushforward

/-! # Cech Pullback Homology -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.CechPullbackHomology

noncomputable section

/-! The actual ordered Cech pullback map, obtained from the geometric adjunction unit. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry.Scheme.Modules

universe u

namespace Construction.CechPullbackMap

variable {X Y S : Scheme.{u}} (f : Y ⟶ X) (π : X ⟶ S) (M : X.Modules)
variable {ι : Type u} [LinearOrder ι] (U : ι → X.Opens)

def map : SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.orderedBaseCechComplex π M U ⟶
    SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.orderedBaseCechComplex (f ≫ π) ((Scheme.Modules.pullback f).obj M) (fun i => f ⁻¹ᵁ U i) :=
  (SheafCohomology.Projective.OrderedBaseCechFunctor.Scheme.Modules.orderedBaseCechComplexFunctor π U).map ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M) ≫
    (SheafCohomology.Projective.OrderedBaseCechPushforward.Scheme.Modules.orderedBaseCechComplexPushforwardIso f π ((Scheme.Modules.pullback f).obj M) U).inv

theorem pushforward_comparison :
    CechPullbackMap.map f π M U ≫
        (SheafCohomology.Projective.OrderedBaseCechPushforward.Scheme.Modules.orderedBaseCechComplexPushforwardIso f π ((Scheme.Modules.pullback f).obj M) U).hom =
      (SheafCohomology.Projective.OrderedBaseCechFunctor.Scheme.Modules.orderedBaseCechComplexFunctor π U).map
        ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M) := by
  let a := (SheafCohomology.Projective.OrderedBaseCechFunctor.Scheme.Modules.orderedBaseCechComplexFunctor π U).map
    ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M)
  let e := SheafCohomology.Projective.OrderedBaseCechPushforward.Scheme.Modules.orderedBaseCechComplexPushforwardIso f π ((Scheme.Modules.pullback f).obj M) U
  exact (Category.assoc a e.inv e.hom).trans
    ((congrArg (fun z => a ≫ z) e.inv_hom_id).trans (Category.comp_id a))

def homologyMap (q : ℕ) :
    (SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.orderedBaseCechComplex π M U).homology q ⟶
      (SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.orderedBaseCechComplex (f ≫ π) ((Scheme.Modules.pullback f).obj M)
        (fun i => f ⁻¹ᵁ U i)).homology q :=
  HomologicalComplex.homologyMap (CechPullbackMap.map f π M U) q

theorem homology_pushforward_comparison (q : ℕ) :
    CechPullbackMap.homologyMap f π M U q ≫ HomologicalComplex.homologyMap
        (SheafCohomology.Projective.OrderedBaseCechPushforward.Scheme.Modules.orderedBaseCechComplexPushforwardIso f π ((Scheme.Modules.pullback f).obj M) U).hom q =
      HomologicalComplex.homologyMap ((SheafCohomology.Projective.OrderedBaseCechFunctor.Scheme.Modules.orderedBaseCechComplexFunctor π U).map
        ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M)) q := by
  exact (HomologicalComplex.homologyMap_comp (CechPullbackMap.map f π M U)
    (SheafCohomology.Projective.OrderedBaseCechPushforward.Scheme.Modules.orderedBaseCechComplexPushforwardIso f π ((Scheme.Modules.pullback f).obj M) U).hom q).symm.trans
      (congrArg (fun z => HomologicalComplex.homologyMap z q) (pushforward_comparison f π M U))

end Construction.CechPullbackMap

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.CechPullbackHomology
