import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Arithmetic.ComplexComparison
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes

/-! # Hom Descent -/

namespace OAI.AlgebraicGeometry.PELModuli.CMPoints.HomDescent

noncomputable section

/-! Additional general graph prerequisite: finitely many complex
homomorphisms between arithmetic abelian varieties descend after one
finite extension, with the specified arithmetic models retained.
There is no CM, good-reduction, torsion, ordinary, or density premise. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

def AbelianHomNumberFieldDescentInput : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (κ : K →+* ℂ) (r m : ℕ)
    (A : Fin r → Over (Spec (.of K))) (groupA : ∀ i, GrpObj (A i)),
    letI (i : Fin r) : GrpObj (A i) := groupA i
    (∀ i, IsCommMonObj (A i)) →
    (∀ i, Smooth (A i).hom ∧ IsProper (A i).hom ∧ GeometricallyConnected (A i).hom) →
    ∀ (source target : Fin m → Fin r)
      (f : ∀ j,
        (Over.pullback (Spec.map (CommRingCat.ofHom κ))).obj (A (source j)) ⟶
          (Over.pullback (Spec.map (CommRingCat.ofHom κ))).obj (A (target j))),
      (∀ j, IsMonHom (f j)) →
      ∃ B : IntegralModel.Base.ArithmeticBaseExtension K κ,
        ∃ fB : ∀ j, (Over.pullback B.fieldExtension).obj (A (source j)) ⟶
          (Over.pullback B.fieldExtension).obj (A (target j)),
          (∀ j, IsMonHom (fB j)) ∧
          ∀ j, (Over.pullback (Spec.map (CommRingCat.ofHom B.embedding))).map (fB j) ≫
              (IntegralModel.Group.BaseChangeComparisons.GroupBaseChange.arithmeticComplexIso B (A (target j))).hom =
            (IntegralModel.Group.BaseChangeComparisons.GroupBaseChange.arithmeticComplexIso B (A (source j))).hom ≫ f j

end

end OAI.AlgebraicGeometry.PELModuli.CMPoints.HomDescent
