import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.RelativeCupPresheafHomotopy
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.SheafLiftHomotopy

/-! # Relative Cup Sheaf Homotopy -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.RelativeCupSheafHomotopy.Constructions

noncomputable section

/-! The actual supported sheaf cup depends only on the relative cohomology class. -/

open _root_.CategoryTheory _root_.CategoryTheory.Preadditive _root_.TopologicalSpace Opposite

set_option backward.isDefEq.respectTransparency false

variable (X : TopCat.{0}) (O : Opens X)
variable (v : (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X (O : Set X)).X 1)
variable (a b : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X (O : Set X)) 2)

def relativeTwoCupGoodShiftSheafHomotopy
    (hv : (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X (O : Set X)).d 1 2 v = a.val-b.val) :
    Homotopy (RelativeCupSheaf.Constructions.relativeTwoCupGoodShiftSheafMap X O a) (RelativeCupSheaf.Constructions.relativeTwoCupGoodShiftSheafMap X O b) := by
  let t := RelativeCupSheaf.Constructions.relativeToSupportedPresheafComplexMap X O
  apply SheafLiftHomotopy.Constructions.sheafLiftTwoGoodShiftHomotopy
    (RelativeCupSheaf.Constructions.relativeTwoCupToSupportedPresheafComplexMap X O a)
    (RelativeCupSheaf.Constructions.relativeTwoCupToSupportedPresheafComplexMap X O b)
    (fun n => RelativeCupPresheafHomotopy.Constructions.relativeOneCupSuccessorPresheafMap X (O : Set X) v n ≫ t.f (2+n))
    (RelativeCupPresheafHomotopy.Constructions.relativeOneCupZeroPresheafMap X (O : Set X) v ≫ t.f 1)
  · change (RelativeCupPresheaf.Constructions.relativeTwoCupPresheafComplexMap X (O : Set X) a).f 0 ≫ t.f 2 -
        (RelativeCupPresheaf.Constructions.relativeTwoCupPresheafComplexMap X (O : Set X) b).f 0 ≫ t.f 2 = _
    rw [← sub_comp, RelativeCupPresheafHomotopy.Constructions.relativeTwoCupPresheafPrimitive_zero X (O : Set X) v a b hv,
      add_comp]
    simp only [Category.assoc]
    rw [← t.comm 1 2]
    rfl
  · intro n
    change (RelativeCupPresheaf.Constructions.relativeTwoCupPresheafComplexMap X (O : Set X) a).f (n+1) ≫ t.f (2+(n+1)) -
        (RelativeCupPresheaf.Constructions.relativeTwoCupPresheafComplexMap X (O : Set X) b).f (n+1) ≫ t.f (2+(n+1)) = _
    rw [← sub_comp, RelativeCupPresheafHomotopy.Constructions.relativeTwoCupPresheafPrimitive_successor X (O : Set X) v a b hv,
      add_comp]
    simp only [Category.assoc]
    rw [← t.comm (2+n) (2+(n+1))]
    rfl

theorem relativeTwoCupGoodShiftSheaf_homotopic_of_class_eq
    (hab : AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X (O : Set X)) 2 a =
      AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X (O : Set X)) 2 b) :
    Nonempty (Homotopy (RelativeCupSheaf.Constructions.relativeTwoCupGoodShiftSheafMap X O a)
      (RelativeCupSheaf.Constructions.relativeTwoCupGoodShiftSheafMap X O b)) := by
  obtain ⟨v,hv⟩ := (AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass_eq_iff_exists_succ
    (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X (O : Set X)) 1 a b).mp hab
  exact ⟨relativeTwoCupGoodShiftSheafHomotopy X O v a b hv⟩

theorem relativeTwoCupGoodShiftSheaf_sections_homologyMap_eq
    (hab : AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X (O : Set X)) 2 a =
      AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X (O : Set X)) 2 b)
    (U : Opens X) (n : ℕ) :
    HomologicalComplex.homologyMap
        (((CycleClass.Geometric.SheafClosedSupport.Cohomology.moduleSheafSections U).mapHomologicalComplex (ComplexShape.up ℕ)).map
          (RelativeCupSheaf.Constructions.relativeTwoCupGoodShiftSheafMap X O a)) n =
      HomologicalComplex.homologyMap
        (((CycleClass.Geometric.SheafClosedSupport.Cohomology.moduleSheafSections U).mapHomologicalComplex (ComplexShape.up ℕ)).map
          (RelativeCupSheaf.Constructions.relativeTwoCupGoodShiftSheafMap X O b)) n := by
  obtain ⟨h⟩ := relativeTwoCupGoodShiftSheaf_homotopic_of_class_eq X O a b hab
  exact ((CycleClass.Geometric.SheafClosedSupport.Cohomology.moduleSheafSections U).mapHomotopy h).homologyMap_eq n

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.RelativeCupSheafHomotopy.Constructions
