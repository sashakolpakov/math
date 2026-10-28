import OAI.AlgebraicGeometry.CycleClass.Geometric.ProjectivePresentation

/-! # Classes -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Classes.Construction

noncomputable section

/-!
# ChernClass: integral codimension-one cycles and their geometric classes

The source consists of finite integer combinations of the project's genuine
codimension-one irreducible supports. Rationalizing the coefficients and
applying the existing geometric cycle-class map defines their Betti classes.

No map from invertible sheaves to these cycles is supplied here. In particular,
this module does not identify this construction with a line bundle's Chern class.
-/

/-- Integral Weil cycles on the actual codimension-one algebraic supports. -/
abbrev IntegralDivisor (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) :=
  X.DimensionCycleSupport 1 →₀ ℤ

/-- Extend each integral multiplicity to a rational multiplicity. -/
def rationalizeDivisor (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) :
    IntegralDivisor X →+ X.RationalDimensionCycle 1 :=
  Finsupp.mapRange.addMonoidHom (Int.castAddHom ℚ)

@[simp]
theorem rationalizeDivisor_single (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)
    (Z : X.DimensionCycleSupport 1) (n : ℤ) :
    rationalizeDivisor X (Finsupp.single Z n) = Finsupp.single Z (n : ℚ) :=
  Finsupp.mapRange_single (hf := (Int.castAddHom ℚ).map_zero)

/-- The Betti class of a divisor, through the existing geometric class map. -/
def divisorGeometricClass (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) :
    IntegralDivisor X →+ X.rationalCohomology 2 :=
  (X.geometricCycleClassMap 1).toAddMonoidHom.comp (rationalizeDivisor X)

theorem divisorGeometricClass_eq (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)
    (D : IntegralDivisor X) :
    divisorGeometricClass X D = X.geometricCycleClassMap 1 (rationalizeDivisor X D) := rfl

@[simp]
theorem divisorGeometricClass_single (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)
    (Z : X.DimensionCycleSupport 1) (n : ℤ) :
    divisorGeometricClass X (Finsupp.single Z n) =
      X.geometricCycleClassMap 1 (Finsupp.single Z (n : ℚ)) := by
  rw [divisorGeometricClass_eq, rationalizeDivisor_single]

/-- Integral divisors generate exactly the existing rational divisor-class subspace. -/
theorem span_divisorGeometricClass (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) :
    Submodule.span ℚ (Set.range (divisorGeometricClass X)) =
      X.geometricAlgebraicClasses 1 := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro a ⟨D, rfl⟩
    exact ⟨rationalizeDivisor X D, rfl⟩
  · rintro a ⟨z, rfl⟩
    induction z using Finsupp.induction_linear with
    | zero => simpa only [map_zero] using
        (Submodule.span ℚ (Set.range (divisorGeometricClass X))).zero_mem
    | add f g hf hg =>
        rw [map_add]
        exact Submodule.add_mem _ hf hg
    | single Z q =>
        rw [← Finsupp.smul_single_one, map_smul]
        apply Submodule.smul_mem
        have h : divisorGeometricClass X (Finsupp.single Z 1) =
            X.geometricCycleClassMap 1 (Finsupp.single Z (1 : ℚ)) := by
          simpa only [Int.cast_one] using divisorGeometricClass_single X Z 1
        exact Submodule.subset_span ⟨Finsupp.single Z 1, h⟩

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Classes.Construction
