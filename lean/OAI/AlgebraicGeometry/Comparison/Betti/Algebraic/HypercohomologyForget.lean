import OAI.AlgebraicGeometry.Comparison.Betti.ComplexHypercohomologyForget
import OAI.AlgebraicGeometry.Comparison.Betti.Algebraic.ComplexSupport

/-! # Hypercohomology Forget -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Algebraic.HypercohomologyForget

noncomputable section

/-! The original algebraic hypercohomology is computed by the actual underlying additive complex. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase)

abbrev AdditiveZariskiSheaves := Sheaf (Opens.grothendieckTopology X.left) AddCommGrpCat.{0}

local instance : HasDerivedCategory.{1} (AdditiveZariskiSheaves X) := HasDerivedCategory.standard _

local instance : (sheafCompose (Opens.grothendieckTopology X.left)
    (forget₂ (ModuleCat.{0} ℂ) AddCommGrpCat.{0})).Additive where
  map_add := by
    intro M N f g
    apply Sheaf.hom_ext
    ext U x
    rfl

def algebraicAdditiveSheafComplexInt : CochainComplex (AdditiveZariskiSheaves X) ℤ :=
  ((sheafCompose (Opens.grothendieckTopology X.left)
    (forget₂ (ModuleCat.{0} ℂ) AddCommGrpCat.{0})).mapHomologicalComplex (.up ℤ)).obj
      (Sheaves.algebraicDeRhamSheafComplexInt X)

instance algebraicAdditiveSheafComplexInt_nonnegative :
    (algebraicAdditiveSheafComplexInt X).IsStrictlyGE 0 :=
  inferInstanceAs
    (CochainComplex.IsStrictlyGE (((sheafCompose (Opens.grothendieckTopology X.left)
      (forget₂ (ModuleCat.{0} ℂ) AddCommGrpCat.{0})).mapHomologicalComplex (.up ℤ)).obj
        (Sheaves.algebraicDeRhamSheafComplexInt X)) 0)

def algebraicHypercohomologyForgetEquiv (n : ℕ) :
    Sheaves.algebraicDeRham X n ≃+
      ((DerivedCategory.singleFunctor (AdditiveZariskiSheaves X) 0).obj
        ((constantSheaf (Opens.grothendieckTopology X.left) AddCommGrpCat.{0}).obj
          (AddCommGrpCat.of ℤ)) ⟶ (DerivedCategory.Q.obj (algebraicAdditiveSheafComplexInt X))⟦(n : ℤ)⟧) :=
  ComplexHypercohomologyForget.Coefficients.coefficientHypercohomologyForgetEquiv (TopCat.of X.left)
    (Sheaves.algebraicDeRhamSheafComplexInt X) (n : ℤ)

end

end OAI.AlgebraicGeometry.Comparison.Betti.Algebraic.HypercohomologyForget
