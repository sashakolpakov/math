import OAI.AlgebraicGeometry.HilbertScheme.Presentations.ModuleCech.CechComplex
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.RingTheory.Finiteness.Basic

/-! # Module Cech Homology -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Bounded.ModuleCechHomology.ProjectiveCech

noncomputable section

/-! The actual Čech cochain complex and its homology vanish above the finite number of chart coordinates. -/

open _root_.MvPolynomial _root_.CategoryTheory

universe u v w

variable {σ : Type u} [Fintype σ] [LinearOrder σ] (R : Type v) [CommRing R]
variable (M : Type w) [AddCommGroup M] [Module R M] [Module (MvPolynomial σ R) M]
  [IsScalarTower R (MvPolynomial σ R) M]
variable (ℳ : ℤ → Submodule R M)
  [SetLike.GradedSMul (WeightedFreeModules.GradedModules.polynomialIntegerGrading (σ := σ) R) ℳ]

omit [LinearOrder σ] [SetLike.GradedSMul (WeightedFreeModules.GradedModules.polynomialIntegerGrading (σ := σ) R) ℳ] in
theorem moduleCechTerm_subsingleton_of_bounded (d : ℤ) (q : ℕ) (hq : Fintype.card σ < q) :
    Subsingleton (ModuleCech.Terms.ProjectiveCech.moduleCechTerm (σ := σ) R M ℳ d q) := by
  constructor
  intro x y
  apply Subtype.ext
  exact (ModuleCech.Card.ProjectiveCech.moduleCech_bounded R M q hq x.val x.property.2).trans
    (ModuleCech.Card.ProjectiveCech.moduleCech_bounded R M q hq y.val y.property.2).symm

theorem moduleCechComplex_exactAt_of_bounded (d : ℤ) (q : ℕ) (hq : Fintype.card σ < q) :
    (ModuleCech.CechComplex.ProjectiveCech.moduleCechComplex (σ := σ) R M ℳ d).ExactAt q := by
  let : Subsingleton ((ModuleCech.CechComplex.ProjectiveCech.moduleCechComplex (σ := σ) R M ℳ d).X q) :=
    moduleCechTerm_subsingleton_of_bounded R M ℳ d q hq
  exact HomologicalComplex.ExactAt.of_isZero (ModuleCat.isZero_of_subsingleton _)

theorem moduleCech_homology_finite_of_bounded (d : ℤ) (q : ℕ) (hq : Fintype.card σ < q) :
    Module.Finite R ((ModuleCech.CechComplex.ProjectiveCech.moduleCechComplex (σ := σ) R M ℳ d).homology q) := by
  let : Subsingleton ((ModuleCech.CechComplex.ProjectiveCech.moduleCechComplex (σ := σ) R M ℳ d).homology q) :=
    ModuleCat.subsingleton_of_isZero (moduleCechComplex_exactAt_of_bounded R M ℳ d q hq).isZero_homology
  infer_instance

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Bounded.ModuleCechHomology.ProjectiveCech
