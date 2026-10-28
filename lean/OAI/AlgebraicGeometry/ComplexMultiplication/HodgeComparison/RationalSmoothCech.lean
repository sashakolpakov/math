import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.RationalSmoothCochains
import OAI.AlgebraicTopology.Cohomology.Singular.SmoothCechDoubleComplex
import OAI.AlgebraicGeometry.DivisorClass.Chern.Rational.CechComparison

/-! # Rational Smooth Cech -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.RationalSmoothCech.CM.Construction

noncomputable section

/-! Rational singular Čech sections map to the native complex smooth
sections by actual coefficient inclusion and restriction to smooth simplices. -/

open _root_.CategoryTheory _root_.TopologicalSpace Opposite
open OAI.AlgebraicTopology.Cohomology.Singular.SmoothCechDoubleComplex
open scoped _root_.Manifold ContDiff

variable (E M : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]

def rationalSmoothCochainMap :
    AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℚ ℚ) (TopCat.of M) ⟶
      PositiveCohomologyConjugation.CM.Construction.restrictComplex (AlgebraicTopology.Cohomology.Singular.ManifoldSmooth.manifoldSmoothCochains E (ModuleCat.of ℂ ℂ) M) :=
  PositiveCohomologyConjugation.CM.Construction.rationalToComplexCochain (TopCat.of M) ≫
    (PositiveCohomologyConjugation.CM.Construction.restrictToRational.mapHomologicalComplex (ComplexShape.up ℕ)).map
      (AlgebraicTopology.Cohomology.Singular.ManifoldSmooth.manifoldSmoothCochainRestriction E (ModuleCat.of ℂ ℂ) M)

theorem rationalSmoothCochainMap_apply (n : ℕ)
    (c : (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℚ ℚ) (TopCat.of M)).X n) :
    (rationalSmoothCochainMap E M).f n c = RationalSmoothCochains.CM.Construction.rationalSmoothCochain E M n c := rfl

variable {I : Type} (U : I → Opens M)

abbrev RationalSingularCechSections (p q : ℕ) :=
  DivisorClass.Chern.Rational.Cech.RationalCech.CechCochain
    (AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularCochainDegreePresheaf (ModuleCat.of ℚ ℚ) (TopCat.of M) q) U p

abbrev ComplexSmoothCechSections (p q : ℕ) :=
  AlgebraicTopology.DeRham.Comparison.SmoothCech.CechCochain (AlgebraicTopology.Cohomology.Singular.ManifoldSmoothPresheaf.manifoldSmoothCochainDegreePresheaf E M (ModuleCat.of ℂ ℂ) q) U p

def rationalSmoothCechCoefficients (p q : ℕ) :
    RationalSingularCechSections M U p q →ₗ[ℚ]
      PositiveCohomologyConjugation.CM.Construction.restrictToRational.obj (ModuleCat.of ℂ (ComplexSmoothCechSections E M U p q)) where
  toFun c a := RationalSmoothCochains.CM.Construction.rationalSmoothCochain E (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a) q (c a)
  map_add' c d := by
    funext a
    exact map_add ((rationalSmoothCochainMap E (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a)).f q).hom (c a) (d a)
  map_smul' r c := by
    funext a
    exact map_smul ((rationalSmoothCochainMap E (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a)).f q).hom r (c a)

theorem rationalSmoothCechCoefficients_apply (p q : ℕ)
    (c : RationalSingularCechSections M U p q) (a : Fin (p + 1) → I) :
    rationalSmoothCechCoefficients E M U p q c a =
      RationalSmoothCochains.CM.Construction.rationalSmoothCochain E (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a) q (c a) := rfl

theorem rationalSmoothCechCoefficients_vertical (p q : ℕ)
    (c : RationalSingularCechSections M U p q) :
    AlgebraicTopology.DeRham.Comparison.SmoothCechDoubleComplex.cechCoefficientMap U ((AlgebraicTopology.Cohomology.Singular.ManifoldSmoothPresheaf.manifoldSmoothPresheafComplex E M (ModuleCat.of ℂ ℂ)).d q (q + 1)) p
      (rationalSmoothCechCoefficients E M U p q c) =
    rationalSmoothCechCoefficients E M U p (q + 1)
      (DivisorClass.Chern.Rational.Cech.RationalCech.cechCoefficientMap U
        ((AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularPresheafComplex (ModuleCat.of ℚ ℚ) (TopCat.of M)).d q (q + 1)) p c) := by
  funext a
  exact RationalSmoothCochains.CM.Construction.rationalSmoothCochain_d E (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a) q (c a)

theorem rationalSmoothCechCoefficients_precomp {p r : ℕ} (q : ℕ)
    (f : Fin (p + 1) → Fin (r + 1)) (c : RationalSingularCechSections M U p q) :
    AlgebraicTopology.DeRham.Comparison.SmoothCech.cechPrecomp (AlgebraicTopology.Cohomology.Singular.ManifoldSmoothPresheaf.manifoldSmoothCochainDegreePresheaf E M (ModuleCat.of ℂ ℂ) q) U f
      (rationalSmoothCechCoefficients E M U p q c) =
      rationalSmoothCechCoefficients E M U r q
        (DivisorClass.Chern.Rational.Cech.RationalCech.cechPrecomp
          (AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularCochainDegreePresheaf (ModuleCat.of ℚ ℚ) (TopCat.of M) q) U f c) := by
  funext a
  exact RationalSmoothCochains.CM.Construction.rationalSmoothCochain_pullback (Opens.inclusion (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le_precomp U a f))
    (contMDiff_inclusion (I := 𝓘(ℝ, E)) (n := ∞) (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le_precomp U a f)) q (c (a ∘ f))

theorem rationalSmoothCechCoefficients_horizontal (p q : ℕ)
    (c : RationalSingularCechSections M U p q) :
    AlgebraicTopology.DeRham.Comparison.SmoothCech.cechDelta (AlgebraicTopology.Cohomology.Singular.ManifoldSmoothPresheaf.manifoldSmoothCochainDegreePresheaf E M (ModuleCat.of ℂ ℂ) q) U p
      (rationalSmoothCechCoefficients E M U p q c) =
      rationalSmoothCechCoefficients E M U (p + 1) q
        (DivisorClass.Chern.Rational.Cech.RationalCech.cechDelta
          (AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularCochainDegreePresheaf (ModuleCat.of ℚ ℚ) (TopCat.of M) q) U p c) := by
  funext a
  let FQ := AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularCochainDegreePresheaf (ModuleCat.of ℚ ℚ) (TopCat.of M) q
  let FC := AlgebraicTopology.Cohomology.Singular.ManifoldSmoothPresheaf.manifoldSmoothCochainDegreePresheaf E M (ModuleCat.of ℂ ℂ) q
  let Rmap := ((rationalSmoothCochainMap E (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a)).f q).hom
  let face : Fin (p + 2) → (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℚ ℚ)
      (TopCat.of (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a))).X q := fun j =>
    (FQ.map (homOfLE (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le_precomp U a j.succAbove)).op).hom (c (a ∘ j.succAbove))
  have hc := AlgebraicTopology.DeRham.Comparison.SmoothCech.cechDelta_apply FC U p (rationalSmoothCechCoefficients E M U p q c) a
  have hq := DivisorClass.Chern.Rational.Cech.RationalCech.cechDelta_apply FQ U p c a
  have hsum : Rmap (∑ j : Fin (p + 2), (-1 : ℤ) ^ j.val • face j) =
      ∑ j : Fin (p + 2), (-1 : ℤ) ^ j.val • Rmap (face j) := by
    rw [map_sum]
    exact Finset.sum_congr rfl (fun j _ => map_zsmul Rmap ((-1 : ℤ) ^ j.val) (face j))
  refine hc.trans ?_
  calc
    _ = ∑ j : Fin (p + 2), (-1 : ℤ) ^ j.val • Rmap (face j) := by
      apply Finset.sum_congr rfl
      intro j _
      apply congrArg (fun z : (AlgebraicTopology.Cohomology.Singular.ManifoldSmooth.manifoldSmoothCochains E (ModuleCat.of ℂ ℂ) (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a)).X q =>
        (-1 : ℤ) ^ j.val • z)
      exact RationalSmoothCochains.CM.Construction.rationalSmoothCochain_pullback (Opens.inclusion (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le_precomp U a j.succAbove))
        (contMDiff_inclusion (I := 𝓘(ℝ, E)) (n := ∞) (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le_precomp U a j.succAbove))
        q (c (a ∘ j.succAbove))
    _ = Rmap (∑ j : Fin (p + 2), (-1 : ℤ) ^ j.val • face j) := hsum.symm
    _ = _ := congrArg Rmap hq.symm

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.RationalSmoothCech.CM.Construction
