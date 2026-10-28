import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.ProjectiveEulerFunction
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.ComplexEulerFormula
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Scalar.FunctorComparison

/-! # Projective Fiber Euler -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.ProjectiveFiberEuler

noncomputable section

/-! The alternating rank function computes the Euler characteristic of every residue-field fiber of a bounded finite projective complex. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits TensorProduct
universe u

theorem finiteProjectiveEulerAt_eq_fiber_sum {R : Type u} [CommRing R]
    (D : CochainComplex (ModuleCat.{u} R) ℕ) (N : ℕ)
    (hfinite : ∀ q, Module.Finite R (D.X q)) (hprojective : ∀ q, Module.Projective R (D.X q))
    (p : PrimeSpectrum R) :
    ProjectiveEulerFunction.finiteProjectiveEulerAt D N p =
      ∑ q ∈ Finset.range N, (-1 : ℤ) ^ q *
        (Module.finrank p.asIdeal.ResidueField
          ((((ModuleCat.extendScalars (algebraMap R p.asIdeal.ResidueField)).mapHomologicalComplex
            (.up ℕ)).obj D).X q) : ℤ) := by
  apply Finset.sum_congr rfl
  intro q _
  have := hfinite q
  have := hprojective q
  have hr := Module.rankAtStalk_eq (M := D.X q) p
  let e := ((Scalar.FunctorComparison.ScalarFunctorComparison.iso R p.asIdeal.ResidueField).app (D.X q)).toLinearEquiv
  exact congrArg (fun n : ℕ => (-1 : ℤ) ^ q * (n : ℤ)) (hr.trans e.finrank_eq)

theorem finiteProjectiveEulerAt_eq_fiberHomology_sum {R : Type u} [CommRing R]
    (D : CochainComplex (ModuleCat.{u} R) ℕ) (N : ℕ)
    (hfinite : ∀ q, Module.Finite R (D.X q)) (hprojective : ∀ q, Module.Projective R (D.X q))
    (hfinal : IsZero (D.X (N + 1))) (p : PrimeSpectrum R) :
    ProjectiveEulerFunction.finiteProjectiveEulerAt D (N + 1) p =
      ∑ q ∈ Finset.range (N + 1), (-1 : ℤ) ^ q *
        (Module.finrank p.asIdeal.ResidueField
          ((((ModuleCat.extendScalars (algebraMap R p.asIdeal.ResidueField)).mapHomologicalComplex
            (.up ℕ)).obj D).homology q) : ℤ) := by
  rw [finiteProjectiveEulerAt_eq_fiber_sum D (N + 1) hfinite hprojective p]
  apply ComplexEulerFormula.cochain_euler_sum_of_final_zero
  · intro q
    have := hfinite q
    have : Module.Finite p.asIdeal.ResidueField
        ((HilbertConstruction.Module.BaseChangeComplex.LocalSectionLifting.moduleBaseChangeFunctor R p.asIdeal.ResidueField).obj (D.X q)) :=
      inferInstanceAs (Module.Finite p.asIdeal.ResidueField (p.asIdeal.ResidueField ⊗[R] D.X q))
    exact Module.Finite.equiv
      ((Scalar.FunctorComparison.ScalarFunctorComparison.iso R p.asIdeal.ResidueField).app (D.X q)).toLinearEquiv
  · exact (ModuleCat.extendScalars (algebraMap R p.asIdeal.ResidueField)).map_isZero hfinal

theorem finiteProjectiveEulerAt_eq_fiber_H0 {R : Type u} [CommRing R]
    (D : CochainComplex (ModuleCat.{u} R) ℕ) (N : ℕ)
    (hfinite : ∀ q, Module.Finite R (D.X q)) (hprojective : ∀ q, Module.Projective R (D.X q))
    (hfinal : IsZero (D.X (N + 1))) (p : PrimeSpectrum R)
    (hexact : ∀ q, (((ModuleCat.extendScalars (algebraMap R p.asIdeal.ResidueField)).mapHomologicalComplex
      (.up ℕ)).obj D).ExactAt (q + 1)) :
    ProjectiveEulerFunction.finiteProjectiveEulerAt D (N + 1) p =
      (Module.finrank p.asIdeal.ResidueField
        ((((ModuleCat.extendScalars (algebraMap R p.asIdeal.ResidueField)).mapHomologicalComplex
          (.up ℕ)).obj D).homology 0) : ℤ) := by
  rw [finiteProjectiveEulerAt_eq_fiber_sum D (N + 1) hfinite hprojective p]
  apply ComplexEulerFormula.cochain_euler_sum_of_positive_exact _ _ _ _ hexact
  · intro q
    have := hfinite q
    have : Module.Finite p.asIdeal.ResidueField
        ((HilbertConstruction.Module.BaseChangeComplex.LocalSectionLifting.moduleBaseChangeFunctor R p.asIdeal.ResidueField).obj (D.X q)) :=
      inferInstanceAs (Module.Finite p.asIdeal.ResidueField (p.asIdeal.ResidueField ⊗[R] D.X q))
    exact Module.Finite.equiv
      ((Scalar.FunctorComparison.ScalarFunctorComparison.iso R p.asIdeal.ResidueField).app (D.X q)).toLinearEquiv
  · exact (ModuleCat.extendScalars (algebraMap R p.asIdeal.ResidueField)).map_isZero hfinal

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.ProjectiveFiberEuler
