import OAI.AlgebraicGeometry.SheafCohomology.ConstantCoefficients
import OAI.AlgebraicGeometry.Comparison.Betti.ExactDerivedAdjunction
import Mathlib.CategoryTheory.Abelian.Exact
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor

/-! # Complex Hypercohomology Forget -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.ComplexHypercohomologyForget.Coefficients

noncomputable section

section

/-! The actual extension of sheaf coefficients from integers to complexes is exact. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace

variable (X : TopCat.{0})

instance complexExtension_additive : (SheafCohomology.Coefficients.Projective.extendComplexSheaf X).Additive :=
  (SheafCohomology.Coefficients.Projective.complexSheafAdjunction X).left_adjoint_additive

instance complexExtension_preservesFiniteColimits :
    PreservesFiniteColimits (SheafCohomology.Coefficients.Projective.extendComplexSheaf X) := by
  have := (SheafCohomology.Coefficients.Projective.complexSheafAdjunction X).isLeftAdjoint
  infer_instance

instance complexExtension_preservesHomology : (SheafCohomology.Coefficients.Projective.extendComplexSheaf X).PreservesHomology :=
  Functor.preservesHomology_of_preservesMonos_and_cokernels _

instance complexExtension_preservesFiniteLimits :
    PreservesFiniteLimits (SheafCohomology.Coefficients.Projective.extendComplexSheaf X) :=
  (SheafCohomology.Coefficients.Projective.extendComplexSheaf X).preservesFiniteLimits_of_preservesHomology

abbrev additiveToInteger := (SheafCohomology.IntegerCoefficients.Projective.integerSheafForget X).asEquivalence.inverse

instance additiveToInteger_additive : (additiveToInteger X).Additive := by
  have : (SheafCohomology.IntegerCoefficients.Projective.integerSheafForget X).asEquivalence.symm.inverse.Additive :=
    inferInstanceAs ((SheafCohomology.IntegerCoefficients.Projective.integerSheafForget X).Additive)
  exact ((SheafCohomology.IntegerCoefficients.Projective.integerSheafForget X).asEquivalence.symm.toAdjunction).left_adjoint_additive

abbrev extendAdditiveComplex := additiveToInteger X ⋙ SheafCohomology.Coefficients.Projective.extendComplexSheaf X

abbrev forgetComplexAdditive := SheafCohomology.Coefficients.Projective.restrictComplexSheaf X ⋙ SheafCohomology.IntegerCoefficients.Projective.integerSheafForget X

def additiveComplexAdjunction : extendAdditiveComplex X ⊣ forgetComplexAdditive X :=
  (SheafCohomology.IntegerCoefficients.Projective.integerSheafForget X).asEquivalence.symm.toAdjunction.comp
    (SheafCohomology.Coefficients.Projective.complexSheafAdjunction X)

def extendedConstantAdditiveIso :
    (extendAdditiveComplex X).obj
      ((constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0}).obj
        (AddCommGrpCat.of ℤ)) ≅
      (constantSheaf (Opens.grothendieckTopology X) (ModuleCat.{0} ℂ)).obj (ModuleCat.of ℂ ℂ) := by
  let I := (constantSheaf (Opens.grothendieckTopology X) (ModuleCat.{0} ℤ)).obj (ModuleCat.of ℤ ℤ)
  let e := (SheafCohomology.IntegerCoefficients.Projective.integerSheafForget X).asEquivalence
  let eI := e.inverse.mapIso (SheafCohomology.ConstantCoefficients.Projective.forgetConstantIntegerIso X).symm ≪≫ e.unitIso.symm.app I
  exact (SheafCohomology.Coefficients.Projective.extendComplexSheaf X).mapIso eI ≪≫ SheafCohomology.ConstantCoefficients.Projective.extendConstantComplexIso X

end

/-! Forgetting complex scalars computes constant-source hypercohomology for whole complexes. -/

open _root_.CategoryTheory _root_.TopologicalSpace

variable (X : TopCat.{0})

abbrev ComplexSheaves := Sheaf (Opens.grothendieckTopology X) (ModuleCat.{0} ℂ)
abbrev AdditiveSheaves := Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0}

local instance : HasDerivedCategory.{1} (ComplexSheaves X) := HasDerivedCategory.standard _
local instance : HasDerivedCategory.{1} (AdditiveSheaves X) := HasDerivedCategory.standard _

def additiveComplexDerivedAdjunction :
    (extendAdditiveComplex X).mapDerivedCategory ⊣ (forgetComplexAdditive X).mapDerivedCategory :=
  ExactDerivedAdjunction.exactAdjunction (additiveComplexAdjunction X)

def coefficientHypercohomologyForgetEquiv (K : CochainComplex (ComplexSheaves X) ℤ) (n : ℤ) :
    ((DerivedCategory.singleFunctor (ComplexSheaves X) 0).obj
        ((constantSheaf (Opens.grothendieckTopology X) (ModuleCat.{0} ℂ)).obj (ModuleCat.of ℂ ℂ)) ⟶
      (DerivedCategory.Q.obj K)⟦n⟧) ≃+
    ((DerivedCategory.singleFunctor (AdditiveSheaves X) 0).obj
        ((constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0}).obj (AddCommGrpCat.of ℤ)) ⟶
      (DerivedCategory.Q.obj
        (((forgetComplexAdditive X).mapHomologicalComplex (.up ℤ)).obj K))⟦n⟧) := by
  let F := extendAdditiveComplex X
  let G := forgetComplexAdditive X
  let A := (constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0}).obj (AddCommGrpCat.of ℤ)
  let eA := (F.mapDerivedCategorySingleFunctor 0).app A ≪≫
    (DerivedCategory.singleFunctor (ComplexSheaves X) 0).mapIso (extendedConstantAdditiveIso X)
  let e₁ := (Linear.homCongr ℤ eA.symm (Iso.refl ((DerivedCategory.Q.obj K)⟦n⟧))).toAddEquiv
  let e₂ := (additiveComplexDerivedAdjunction X).homAddEquiv
    ((DerivedCategory.singleFunctor (AdditiveSheaves X) 0).obj A) ((DerivedCategory.Q.obj K)⟦n⟧)
  let eK := (G.mapDerivedCategory.commShiftIso n).app (DerivedCategory.Q.obj K) ≪≫
    (shiftFunctor (DerivedCategory (AdditiveSheaves X)) n).mapIso
      (G.mapDerivedCategoryFactors.app K)
  exact e₁.trans (e₂.trans (Linear.homCongr ℤ (Iso.refl _) eK).toAddEquiv)

end

end OAI.AlgebraicGeometry.Comparison.Betti.ComplexHypercohomologyForget.Coefficients
