import OAI.AlgebraicGeometry.SheafCohomology.Projective.InvertibleEvaluation
import OAI.AlgebraicGeometry.SheafCohomology.Projective.TensorSections
import Mathlib.CategoryTheory.Equivalence

/-! # Invertible Tensor Equivalence -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.InvertibleTensorEquivalence

noncomputable section

/-! Tensoring by a locally trivial rank-one sheaf is an equivalence of module categories. -/

open _root_.CategoryTheory MonoidalCategory _root_.AlgebraicGeometry
universe u v

def tensorLeftEquivalenceOfInverse
    {C : Type u} [Category.{v} C] [MonoidalCategory C]
    (M N : C) (e : M ⊗ N ≅ 𝟙_ C) (f : N ⊗ M ≅ 𝟙_ C) : C ≌ C :=
  CategoryTheory.Equivalence.mk (tensorLeft M) (tensorLeft N)
    ((tensorLeftTensor N M).symm ≪≫ (curriedTensor C).mapIso f ≪≫
      leftUnitorNatIso C).symm
    ((tensorLeftTensor M N).symm ≪≫ (curriedTensor C).mapIso e ≪≫
      leftUnitorNatIso C)

def invertibleTensorEquivalence {X : Scheme.{u}} (M : X.Modules)
    (hM : Invertible.Scheme.Modules.IsInvertible M) : X.Modules ≌ X.Modules := by
  letI := Monoidal.Scheme.Modules.monoidalCategory X
  letI := Monoidal.Scheme.Modules.symmetricCategory X
  let e : M ⊗ Dual.Scheme.Modules.dualObj M ≅ 𝟙_ X.Modules :=
    TensorSections.monoidalTensorObjIso M (Dual.Scheme.Modules.dualObj M) ≪≫
      InvertibleEvaluation.Scheme.Modules.invertibleEvaluationIso hM ≪≫ (TensorSections.monoidalUnitObjIso X).symm
  exact tensorLeftEquivalenceOfInverse M (Dual.Scheme.Modules.dualObj M) e
    (β_ (Dual.Scheme.Modules.dualObj M) M ≪≫ e)

theorem invertibleTensorEquivalence_obj {X : Scheme.{u}} (M : X.Modules)
    (hM : Invertible.Scheme.Modules.IsInvertible M) (N : X.Modules) :
    letI := Monoidal.Scheme.Modules.monoidalCategory X
    (invertibleTensorEquivalence M hM).functor.obj N = M ⊗ N := rfl

def invertibleRightTensorEquivalence {X : Scheme.{u}} (M : X.Modules)
    (hM : Invertible.Scheme.Modules.IsInvertible M) : X.Modules ≌ X.Modules := by
  letI := Monoidal.Scheme.Modules.monoidalCategory X
  letI := Monoidal.Scheme.Modules.symmetricCategory X
  exact (invertibleTensorEquivalence M hM).changeFunctor
    (BraidedCategory.tensorLeftIsoTensorRight M)

theorem invertibleRightTensorEquivalence_obj {X : Scheme.{u}} (M : X.Modules)
    (hM : Invertible.Scheme.Modules.IsInvertible M) (N : X.Modules) :
    letI := Monoidal.Scheme.Modules.monoidalCategory X
    (invertibleRightTensorEquivalence M hM).functor.obj N = N ⊗ M := rfl

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.InvertibleTensorEquivalence
