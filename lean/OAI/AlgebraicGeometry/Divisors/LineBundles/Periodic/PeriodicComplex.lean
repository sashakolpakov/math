import Mathlib.Algebra.Homology.HomologySequence
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import OAI.AlgebraicGeometry.Divisors.LineBundles.CyclicExactLength

/-! # Periodic Complex -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Periodic.PeriodicComplex.BundleCycles

noncomputable section

section

/-!
# LineBundleCycles: actual two-periodic complexes of modules

The two indices form a circle. Two endomorphisms with zero composites
give an actual homological complex, so its homology and connecting maps
are those of the usual kernel/quotient construction.
-/

open _root_.CategoryTheory

def periodicComplexShape : ComplexShape Bool where
  Rel i j := i ≠ j
  next_eq := by decide
  prev_eq := by decide

theorem periodicComplexShape_false_true : periodicComplexShape.Rel false true := by
  change false ≠ true
  decide

theorem periodicComplexShape_true_false : periodicComplexShape.Rel true false := by
  change true ≠ false
  decide

variable {R : Type*} [CommRing R]

def endomorphismPeriodicComplex {M : Type*} [AddCommGroup M] [Module R M]
    (φ ψ : M →ₗ[R] M) (hφψ : ψ.comp φ = 0) (hψφ : φ.comp ψ = 0) :
    HomologicalComplex (ModuleCat R) periodicComplexShape where
  X _ := ModuleCat.of R M
  d i j := match i, j with
    | false, true => ModuleCat.ofHom φ
    | true, false => ModuleCat.ofHom ψ
    | _, _ => 0
  shape := by
    intro i j hij
    cases i <;> cases j <;> simp_all [periodicComplexShape]
  d_comp_d' := by
    intro i j k hij hjk
    cases i <;> cases j <;> cases k <;>
      simp_all [periodicComplexShape, ← ModuleCat.ofHom_comp]

/-- The Herbrand Euler length, with both homology lengths finite. -/
def periodicEulerLength (K : HomologicalComplex (ModuleCat R) periodicComplexShape)
    (_h₀ : Module.length R (K.homology false) ≠ ⊤)
    (_h₁ : Module.length R (K.homology true) ≠ ⊤) : ℤ :=
  ((Module.length R (K.homology false)).toNat : ℤ) -
    (Module.length R (K.homology true)).toNat

end

/-!
# LineBundleCycles: additivity from the actual periodic homology sequence

The connecting maps are the snake connecting maps of the short exact
sequence of complexes. The cyclic six-term length identity then gives
additivity of the Herbrand Euler length.
-/

open _root_.CategoryTheory _root_.HomologicalComplex

variable {R : Type*} [CommRing R]

theorem periodicEulerLength_additive
    (S : ShortComplex (HomologicalComplex (ModuleCat R) periodicComplexShape))
    (hS : S.ShortExact)
    (hA₀ : Module.length R (S.X₁.homology false) ≠ ⊤)
    (hA₁ : Module.length R (S.X₁.homology true) ≠ ⊤)
    (hB₀ : Module.length R (S.X₂.homology false) ≠ ⊤)
    (hB₁ : Module.length R (S.X₂.homology true) ≠ ⊤)
    (hC₀ : Module.length R (S.X₃.homology false) ≠ ⊤)
    (hC₁ : Module.length R (S.X₃.homology true) ≠ ⊤) :
    periodicEulerLength S.X₂ hB₀ hB₁ =
      periodicEulerLength S.X₁ hA₀ hA₁ + periodicEulerLength S.X₃ hC₀ hC₁ := by
  have he := CyclicExactLength.BundleCycles.moduleLengthNat_cyclicSixTerm
    (homologyMap S.f false).hom (homologyMap S.g false).hom
    (hS.δ false true periodicComplexShape_false_true).hom
    (homologyMap S.f true).hom (homologyMap S.g true).hom
    (hS.δ true false periodicComplexShape_true_false).hom
    ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp
      (hS.homology_exact₂ false))
    ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp
      (hS.homology_exact₃ false true periodicComplexShape_false_true))
    ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp
      (hS.homology_exact₁ false true periodicComplexShape_false_true))
    ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp
      (hS.homology_exact₂ true))
    ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp
      (hS.homology_exact₃ true false periodicComplexShape_true_false))
    ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp
      (hS.homology_exact₁ true false periodicComplexShape_true_false))
    hA₀ hB₀ hC₀ hA₁ hB₁ hC₁
  unfold periodicEulerLength
  omega

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Periodic.PeriodicComplex.BundleCycles
