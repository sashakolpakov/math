import OAI.AlgebraicGeometry.Comparison.Betti.ExtDerivedPullback
import OAI.AlgebraicGeometry.Comparison.Betti.SingularExtNaturality

/-! # Sheaf Naturality -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Derived.SheafNaturality

noncomputable section

/-! Naturality of the existing, explicitly constructed derived-sheaf-to-Betti comparison. -/

open _root_.CategoryTheory _root_.TopologicalSpace

variable (M : TopCat.{0}) [StronglyLocallyContractibleSpace M] [MetrizableSpace M]

theorem singularDerivedConstantLinearEquiv_factor (n : ℕ)
    (a : AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℂ ℂ) M n) :
    DerivedSheafBetti.singularDerivedConstantLinearEquiv M n a =
      ExtDerivedPullback.locallyConstantExtDerivedEquiv M n (SingularExtNaturality.singularLocallyConstantExtEquiv M n a) := rfl

variable {M} {N : TopCat.{0}} [StronglyLocallyContractibleSpace N] [MetrizableSpace N] (f : M ⟶ N)

theorem singularDerivedConstantLinearEquiv_naturality (n : ℕ)
    (a : AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℂ ℂ) N n) :
    DerivedSheafBetti.singularDerivedConstantLinearEquiv M n
        (HomologicalComplex.homologyMap (AlgebraicTopology.Cohomology.Singular.Functor.singularPullback (ModuleCat.of ℂ ℂ) f) n a) =
      ConstantPullback.constantDerivedPullback f n (DerivedSheafBetti.singularDerivedConstantLinearEquiv N n a) := by
  rw [singularDerivedConstantLinearEquiv_factor M n, singularDerivedConstantLinearEquiv_factor N n,
    SingularExtNaturality.singularLocallyConstantExtEquiv_naturality f n a]
  exact ExtDerivedPullback.locallyConstantExtDerivedEquiv_naturality f n _

theorem singularConstantCohomologyIso_naturality (n : ℕ) :
    (ModuleCat.uliftFunctor.{1, 0} ℂ).map
        (HomologicalComplex.homologyMap (AlgebraicTopology.Cohomology.Singular.Functor.singularPullback (ModuleCat.of ℂ ℂ) f) n) ≫
      (DerivedSheafBetti.singularConstantCohomologyIso M n).hom =
    (DerivedSheafBetti.singularConstantCohomologyIso N n).hom ≫ ConstantPullback.constantDerivedPullback f n := by
  ext a
  exact singularDerivedConstantLinearEquiv_naturality f n a.down

end

end OAI.AlgebraicGeometry.Comparison.Betti.Derived.SheafNaturality
