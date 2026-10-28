import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Cech.ModuleIsomorphism
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Graded.CechVanishing
import Mathlib.LinearAlgebra.Finsupp.Pi

/-! # Module Cech -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Polynomial.ModuleCech.ProjectiveCech

noncomputable section

/-! The polynomial ring, as its actual module, has exact augmented Čech complex in nonnegative degrees. -/

open _root_.MvPolynomial

universe u v

variable {σ : Type v} [Fintype σ] [LinearOrder σ] [Nonempty σ]
variable (R : Type u) [CommRing R]

theorem polynomialModuleCech_exactAt (d : ℤ) (hd : 0 ≤ d) (q : ℕ) :
    Cech.DimensionShift.ProjectiveCech.ModuleCechExactAt (σ := σ) R (MvPolynomial σ R) (WeightedFreeModules.GradedModules.polynomialIntegerGrading R) d q := by
  let ι := PUnit.{max u v + 1}
  let E := Finsupp.uniqueLinearEquiv (MvPolynomial σ R) (MvPolynomial σ R) (default : ι)
  have he (a : ℤ) (f : ι →₀ MvPolynomial σ R)
      (hf : f ∈ WeightedFreeModules.GradedModules.weightedFreeGrading R (fun _ : ι => (0 : ℤ)) a) :
      E f ∈ WeightedFreeModules.GradedModules.polynomialIntegerGrading R a := by
    have h := (WeightedFreeModules.GradedModules.mem_weightedFreeGrading R (fun _ : ι => (0 : ℤ)) a f).mp hf default
    simpa only [E, Finsupp.uniqueLinearEquiv_apply, sub_zero] using h
  apply (Cech.ModuleIsomorphism.ProjectiveCech.moduleCechExactAt_iff_of_module_bijective R (WeightedFreeModules.GradedModules.weightedFreeGrading R (fun _ : ι => (0 : ℤ)))
    (WeightedFreeModules.GradedModules.polynomialIntegerGrading R) E.toLinearMap he E.bijective d q).mp
  apply Graded.CechVanishing.ProjectiveCech.freeModuleCech_exactAt R ι (fun _ => 0) d _ q
  simpa only [FreeModuleCechExactness.ProjectiveCech.freeCechDegreeBound, Int.toNat_zero, Finset.sum_const_zero, Nat.cast_zero] using hd

omit [Fintype σ] [Nonempty σ] in
theorem moduleCechExactAt_of_subsingleton (M : Type*) [AddCommGroup M] [Module R M]
    [Module (MvPolynomial σ R) M] [IsScalarTower R (MvPolynomial σ R) M] [Subsingleton M]
    (ℳ : ℤ → Submodule R M) (d : ℤ) (q : ℕ) :
    Cech.DimensionShift.ProjectiveCech.ModuleCechExactAt (σ := σ) R M ℳ d q := by
  intro f _ _ _
  have hf : f = 0 := by
    funext s
    apply Subsingleton.elim
  refine ⟨0, fun _ => Submodule.zero_mem _, fun _ _ => rfl, ?_⟩
  rw [map_zero, hf]

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Polynomial.ModuleCech.ProjectiveCech
