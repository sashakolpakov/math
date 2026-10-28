/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project

ForMathlib (OURS, not vendored): upstream candidate.
This file has been modified.
-/
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Noetherian.FiniteExact
import Mathlib.Algebra.Homology.HomologySequence
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-! # Homology Exact Sequences -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.HomologyExactSequences.FiniteHomology

noncomputable section

/-

ForMathlib (OURS, not vendored): upstream candidate.
-/

open _root_.CategoryTheory

universe u v w

variable {R : Type u} [CommRing R] [IsNoetherianRing R]
variable {ι : Type w} {c : ComplexShape ι}
variable {S : ShortComplex (HomologicalComplex (ModuleCat.{v} R) c)}

/-- In a short exact sequence of complexes, finite homology of the third complex in one
degree and of the second complex in the following degree imply finite homology of the first
complex in the following degree. -/
theorem finite_homology_X1 (hS : S.ShortExact) (i j : ι) (hij : c.Rel i j)
    [Module.Finite R (S.X₃.homology i)] [Module.Finite R (S.X₂.homology j)] :
    Module.Finite R (S.X₁.homology j) :=
  Noetherian.FiniteExact.noetherian_finite_of_exact _ _
    ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp
      (hS.homology_exact₁ i j hij))

/-- At a degree with no predecessor, finite homology of the middle complex implies finite
homology of the first complex. -/
theorem finite_homology_X1_of_not_rel (hS : S.ShortExact) (j : ι)
    (hj : ∀ i, ¬ c.Rel i j) [Module.Finite R (S.X₂.homology j)] :
    Module.Finite R (S.X₁.homology j) := by
  let := hS.mono_f
  let : Mono (HomologicalComplex.homologyMap S.f j) :=
    HomologicalComplex.mono_homologyMap_of_mono_of_not_rel S.f j hj
  exact Module.Finite.of_injective (HomologicalComplex.homologyMap S.f j).hom
    ((ModuleCat.mono_iff_injective (HomologicalComplex.homologyMap S.f j)).mp inferInstance)

/-- In a short exact sequence of complexes, finite homology of the first and third
complexes in one degree implies finite homology of the second complex in that degree. -/
theorem finite_homology_X2 (hS : S.ShortExact) (i : ι)
    [Module.Finite R (S.X₁.homology i)] [Module.Finite R (S.X₃.homology i)] :
    Module.Finite R (S.X₂.homology i) :=
  Noetherian.FiniteExact.noetherian_finite_of_exact _ _
    ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp
      (hS.homology_exact₂ i))

/-- In a short exact sequence of complexes, finite homology of the second complex in one
degree and of the first complex in the following degree imply finite homology of the third
complex in the first degree. -/
theorem finite_homology_X3 (hS : S.ShortExact) (i j : ι) (hij : c.Rel i j)
    [Module.Finite R (S.X₂.homology i)] [Module.Finite R (S.X₁.homology j)] :
    Module.Finite R (S.X₃.homology i) :=
  Noetherian.FiniteExact.noetherian_finite_of_exact _ _
    ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp
      (hS.homology_exact₃ i j hij))

/-- In a short exact sequence of cochain complexes indexed by the natural numbers, finite
homology of the middle and third complexes in every degree implies finite homology of the
first complex in every degree. -/
theorem finite_homology_X1_up_nat
    {S : ShortComplex (CochainComplex (ModuleCat.{v} R) ℕ)} (hS : S.ShortExact)
    [∀ n, Module.Finite R (S.X₂.homology n)] [∀ n, Module.Finite R (S.X₃.homology n)]
    (n : ℕ) : Module.Finite R (S.X₁.homology n) := by
  cases n with
  | zero =>
      apply finite_homology_X1_of_not_rel hS 0
      simp [ComplexShape.up_Rel]
  | succ n =>
      exact finite_homology_X1 hS n (n + 1) (by simp [ComplexShape.up_Rel])

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.HomologyExactSequences.FiniteHomology
