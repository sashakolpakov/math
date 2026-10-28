import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.NeronSpecialization
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.FiberGeneration

/-! # Point Specialization Formula -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.HodgeConjecture.HeckeCycles.PointSpecializationFormula.CM.Points

/-! Evaluation and base change commute for the actual functor of points.
Together with HomExtension this proves compatibility of specialization with
endomorphism evaluation on integral points. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GroupBaseChange.CM

variable {S S' : Scheme} (G : CommGrp (Over S))

def evaluateAt (T : Over S) : AbelianScheme.TateComparison.End.IntegralEnd G.X →+* AddMonoid.End (Additive (T ⟶ G.X)) where
  toFun f := (f.app (.op T)).hom
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

def pointBaseChange (b : S' ⟶ S) (T : Over S) :
    Additive (T ⟶ G.X) →+ Additive ((Over.pullback b).obj T ⟶ (GroupBaseChange.CM.changedGroup G b).X) where
  toFun x := Additive.ofMul ((Over.pullback b).map x.toMul)
  map_zero' := (Over.pullback b).map_one
  map_add' x y := (Over.pullback b).map_mul x.toMul y.toMul

theorem pointBaseChange_evaluate (b : S' ⟶ S) (T : Over S)
    (f : AbelianScheme.TateComparison.End.IntegralEnd G.X) (x : Additive (T ⟶ G.X)) :
    pointBaseChange G b T (evaluateAt G T f x) =
      evaluateAt (GroupBaseChange.CM.changedGroup G b) ((Over.pullback b).obj T) (AbelianScheme.TateComparison.BaseChange.endBaseChange G.X b f)
        (pointBaseChange G b T x) := by
  let : GrpObj (GroupBaseChange.CM.changedGroup G b).X := (GroupBaseChange.CM.changedGroup G b).grp
  let : IsCommMonObj (GroupBaseChange.CM.changedGroup G b).X := (GroupBaseChange.CM.changedGroup G b).comm
  apply Additive.toMul.injective
  change (Over.pullback b).map (((f.app (.op T)).hom x).toMul) =
    (((AbelianScheme.TateComparison.BaseChange.endBaseChange G.X b f).app (.op ((Over.pullback b).obj T))).hom
      (Additive.ofMul ((Over.pullback b).map x.toMul))).toMul
  exact (congrArg (Over.pullback b).map (AbelianScheme.TateComparison.End.endSchemeMap_points G.X f T x.toMul)).trans
    (((Over.pullback b).map_comp x.toMul (AbelianScheme.TateComparison.End.endSchemeMap G.X f)).trans
      ((congrArg ((Over.pullback b).map x.toMul ≫ ·)
        (AbelianScheme.TateComparison.BaseChange.endBaseChange_schemeMap G.X b f).symm).trans
        (@AbelianScheme.TateComparison.End.endSchemeMap_points S' (GroupBaseChange.CM.changedGroup G b).X
          (GroupBaseChange.CM.changedGroup G b).grp (GroupBaseChange.CM.changedGroup G b).comm (AbelianScheme.TateComparison.BaseChange.endBaseChange G.X b f)
          ((Over.pullback b).obj T) ((Over.pullback b).map x.toMul)).symm))

theorem evaluate_precomp {T U : Over S} (p : T ⟶ U)
    (f : AbelianScheme.TateComparison.End.IntegralEnd G.X) (x : Additive (U ⟶ G.X)) :
    evaluateAt G T f (Additive.ofMul (p ≫ x.toMul)) =
      Additive.ofMul (p ≫ (evaluateAt G U f x).toMul) := by
  apply Additive.toMul.injective
  change ((f.app (.op T)).hom (Additive.ofMul (p ≫ x.toMul))).toMul =
    p ≫ ((f.app (.op U)).hom x).toMul
  exact (AbelianScheme.TateComparison.End.endSchemeMap_points G.X f T (p ≫ x.toMul)).trans
    ((Category.assoc p x.toMul (AbelianScheme.TateComparison.End.endSchemeMap G.X f)).trans
      (congrArg (p ≫ ·) (AbelianScheme.TateComparison.End.endSchemeMap_points G.X f U x.toMul).symm))

variable {R K : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field K] [Algebra R K] [IsFractionRing R K]
  (A : CommGrp (Over (Spec (.of R))))
  [Smooth A.X.hom] [IsProper A.X.hom] [GeometricallyConnected A.X.hom]

open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.NeronSpecialization.CM

def genericActionOnIntegralPoints (T : Over (Spec (.of R))) :
    AbelianScheme.TateComparison.End.IntegralEnd (GroupBaseChange.CM.changedGroup A (NeronSpecialization.CM.genericBase (R := R) (K := K))).X →+*
      AddMonoid.End (Additive (T ⟶ A.X)) :=
  (evaluateAt A T).comp (NeronSpecialization.CM.genericEndEquiv A).symm.toRingHom

theorem specialization_evaluation {k : Type} [Field k] (res : R →+* k)
    (T : Over (Spec (.of R)))
    (f : AbelianScheme.TateComparison.End.IntegralEnd (GroupBaseChange.CM.changedGroup A (NeronSpecialization.CM.genericBase (R := R) (K := K))).X)
    (x : Additive (T ⟶ A.X)) :
    pointBaseChange A (Spec.map (CommRingCat.ofHom res)) T
        (genericActionOnIntegralPoints A T f x) =
      evaluateAt (GroupBaseChange.CM.changedGroup A (Spec.map (CommRingCat.ofHom res)))
        ((Over.pullback (Spec.map (CommRingCat.ofHom res))).obj T)
        (NeronSpecialization.CM.specialization A res f)
        (pointBaseChange A (Spec.map (CommRingCat.ofHom res)) T x) :=
  pointBaseChange_evaluate A (Spec.map (CommRingCat.ofHom res)) T
    ((NeronSpecialization.CM.genericEndEquiv A).symm f) x

end AlgebraicGeometry.HodgeConjecture.HeckeCycles.PointSpecializationFormula.CM.Points

namespace AlgebraicGeometry.HodgeConjecture.HeckeCycles.PointSpecializationFormula.CM.Test

/-! Pointwise endomorphism and multiset identities are natural in the
test scheme. This retains all terms when identifying evaluated generic bases. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.PointSpecializationFormula.CM.Points

variable {S : Scheme} (G : CommGrp (Over S)) {T U : Over S} (p : U ⟶ T)

def precompose : Additive (T ⟶ G.X) →+ Additive (U ⟶ G.X) where
  toFun x := Additive.ofMul (p ≫ x.toMul)
  map_zero' := MonObj.comp_one p
  map_add' x y := MonObj.comp_mul p x.toMul y.toMul

theorem precompose_apply (x : T ⟶ G.X) :
    precompose G p (Additive.ofMul x) = Additive.ofMul (p ≫ x) := rfl

theorem precompose_evaluate (f : AbelianScheme.TateComparison.End.IntegralEnd G.X) (x : Additive (T ⟶ G.X)) :
    precompose G p (Points.evaluateAt G T f x) = Points.evaluateAt G U f (precompose G p x) :=
  (Points.evaluate_precomp G p f x).symm

theorem neighbor_formula {X : Over S} (a : X ⟶ G.X) (f : AbelianScheme.TateComparison.End.IntegralEnd G.X)
    (x y : T ⟶ X) (Nx Ny : Multiset (T ⟶ X))
    (h : Points.evaluateAt G T f (Additive.ofMul (x ≫ a) - Additive.ofMul (y ≫ a)) =
      (Nx.map (fun z => Additive.ofMul (z ≫ a))).sum -
        (Ny.map (fun z => Additive.ofMul (z ≫ a))).sum) :
    Points.evaluateAt G U f (Additive.ofMul ((p ≫ x) ≫ a) - Additive.ofMul ((p ≫ y) ≫ a)) =
      (Nx.map (fun z => Additive.ofMul ((p ≫ z) ≫ a))).sum -
        (Ny.map (fun z => Additive.ofMul ((p ≫ z) ≫ a))).sum := by
  have hp := congrArg (precompose G p) h
  rw [precompose_evaluate] at hp
  simpa only [map_sub, map_multiset_sum, Multiset.map_map, Function.comp_def,
    precompose_apply, Category.assoc] using hp

end AlgebraicGeometry.HodgeConjecture.HeckeCycles.PointSpecializationFormula.CM.Test

namespace AlgebraicGeometry.HodgeConjecture.HeckeCycles.PointSpecializationFormula.CM.Descent

/-! An actual point equation descends along an epimorphism of test
schemes. This permits finite evaluation before proper specialization. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.PointSpecializationFormula.CM.Points
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.PointSpecializationFormula.CM.Test

variable {S : Scheme} (G : CommGrp (Over S)) {T U : Over S} (p : U ⟶ T) [Epi p]

theorem precompose_injective : Function.Injective (Test.precompose G p) := by
  intro x y h
  apply Additive.toMul.injective
  exact (cancel_epi p).mp (congrArg Additive.toMul h)

theorem neighbor_formula_of_precompose {X : Over S} (a : X ⟶ G.X) (f : AbelianScheme.TateComparison.End.IntegralEnd G.X)
    (x y : T ⟶ X) (Nx Ny : Multiset (T ⟶ X))
    (h : Points.evaluateAt G U f
      (Additive.ofMul ((p ≫ x) ≫ a) - Additive.ofMul ((p ≫ y) ≫ a)) =
      (Nx.map (fun z => Additive.ofMul ((p ≫ z) ≫ a))).sum -
        (Ny.map (fun z => Additive.ofMul ((p ≫ z) ≫ a))).sum) :
    Points.evaluateAt G T f (Additive.ofMul (x ≫ a) - Additive.ofMul (y ≫ a)) =
      (Nx.map (fun z => Additive.ofMul (z ≫ a))).sum -
        (Ny.map (fun z => Additive.ofMul (z ≫ a))).sum := by
  apply precompose_injective G p
  rw [Test.precompose_evaluate]
  simp only [map_sub, map_multiset_sum, Multiset.map_map, Function.comp_def,
    Test.precompose_apply]
  simpa only [Category.assoc, map_sub] using h

end AlgebraicGeometry.HodgeConjecture.HeckeCycles.PointSpecializationFormula.CM.Descent

end

end OAI
