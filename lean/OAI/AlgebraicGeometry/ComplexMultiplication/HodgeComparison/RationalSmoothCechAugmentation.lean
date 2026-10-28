import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.RationalSmoothCech
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.RationalTotalMap

/-! # Rational Smooth Cech Augmentation -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.RationalSmoothCechAugmentation.CM.Construction

noncomputable section

section

/-! The actual rational singular Čech total complex maps to the
native complex smooth total complex with its coefficients restricted to ℚ. -/

open _root_.CategoryTheory _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

variable (E M : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] {I : Type} (U : I → Opens M)

def rationalSmoothCechComponent (p q : ℕ) :
    ((DivisorClass.Chern.Rational.CechComparison.RationalCech.singularCechDoubleComplex (TopCat.of M) U (ModuleCat.of ℚ ℚ)).X p).X q ⟶
      PositiveCohomologyConjugation.CM.Construction.restrictToRational.obj (((AlgebraicTopology.Cohomology.Singular.SmoothCechDoubleComplex.manifoldSmoothCechDoubleComplex E M U (ModuleCat.of ℂ ℂ)).X p).X q) := by
  change ModuleCat.of ℚ (RationalSmoothCech.CM.Construction.RationalSingularCechSections M U p q) ⟶
    PositiveCohomologyConjugation.CM.Construction.restrictToRational.obj (ModuleCat.of ℂ (RationalSmoothCech.CM.Construction.ComplexSmoothCechSections E M U p q))
  exact ConcreteCategory.ofHom (C := ModuleCat.{0} ℚ)
    (X := ModuleCat.of ℚ (RationalSmoothCech.CM.Construction.RationalSingularCechSections M U p q))
    (Y := PositiveCohomologyConjugation.CM.Construction.restrictToRational.obj (ModuleCat.of ℂ (RationalSmoothCech.CM.Construction.ComplexSmoothCechSections E M U p q)))
    (RationalSmoothCech.CM.Construction.rationalSmoothCechCoefficients E M U p q)

theorem rationalSmoothCechComponent_horizontal (p q : ℕ) :
    ((DivisorClass.Chern.Rational.CechComparison.RationalCech.singularCechDoubleComplex (TopCat.of M) U (ModuleCat.of ℚ ℚ)).d p (p + 1)).f q ≫
      rationalSmoothCechComponent E M U (p + 1) q =
    rationalSmoothCechComponent E M U p q ≫ PositiveCohomologyConjugation.CM.Construction.restrictToRational.map
      (((AlgebraicTopology.Cohomology.Singular.SmoothCechDoubleComplex.manifoldSmoothCechDoubleComplex E M U (ModuleCat.of ℂ ℂ)).d p (p + 1)).f q) := by
  rw [DivisorClass.Chern.Rational.CechComparison.RationalCech.singularCechDoubleComplex_d_f,
    AlgebraicTopology.Cohomology.Singular.SmoothCechDoubleComplex.manifoldSmoothCechDoubleComplex_d_f]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro c
  exact (RationalSmoothCech.CM.Construction.rationalSmoothCechCoefficients_horizontal E M U p q c).symm

theorem rationalSmoothCechComponent_vertical (p q : ℕ) :
    ((DivisorClass.Chern.Rational.CechComparison.RationalCech.singularCechDoubleComplex (TopCat.of M) U (ModuleCat.of ℚ ℚ)).X p).d q (q + 1) ≫
      rationalSmoothCechComponent E M U p (q + 1) =
    rationalSmoothCechComponent E M U p q ≫ PositiveCohomologyConjugation.CM.Construction.restrictToRational.map
      (((AlgebraicTopology.Cohomology.Singular.SmoothCechDoubleComplex.manifoldSmoothCechDoubleComplex E M U (ModuleCat.of ℂ ℂ)).X p).d q (q + 1)) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro c
  exact (RationalSmoothCech.CM.Construction.rationalSmoothCechCoefficients_vertical E M U p q c).symm

def rationalSmoothCechTotalMap :
    DivisorClass.Chern.Rational.CechComparison.RationalCech.singularCechTotal (TopCat.of M) U (ModuleCat.of ℚ ℚ) ⟶
      PositiveCohomologyConjugation.CM.Construction.restrictComplex (AlgebraicTopology.Cohomology.Singular.SmoothCechDoubleComplex.manifoldSmoothCechTotal E M U (ModuleCat.of ℂ ℂ)) :=
  RationalTotalMap.CM.Construction.rationalComplexTotalMap
    (DivisorClass.Chern.Rational.CechComparison.RationalCech.singularCechDoubleComplex (TopCat.of M) U (ModuleCat.of ℚ ℚ))
    (AlgebraicTopology.Cohomology.Singular.SmoothCechDoubleComplex.manifoldSmoothCechDoubleComplex E M U (ModuleCat.of ℂ ℂ))
    (rationalSmoothCechComponent E M U)
    (rationalSmoothCechComponent_horizontal E M U) (rationalSmoothCechComponent_vertical E M U)

theorem rationalSmoothCechTotalMap_iota (p q n : ℕ) (h : p + q = n)
    (c : RationalSmoothCech.CM.Construction.RationalSingularCechSections M U p q) :
    (rationalSmoothCechTotalMap E M U).f n
      (DivisorClass.Chern.Rational.Cech.RationalCech.cechTotalInclusion U
        (AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularPresheafComplex (ModuleCat.of ℚ ℚ) (TopCat.of M)) p q n h c) =
    AlgebraicTopology.DeRham.Comparison.CechTotalFunctor.cechTotalInclusion U (AlgebraicTopology.Cohomology.Singular.ManifoldSmoothPresheaf.manifoldSmoothPresheafComplex E M (ModuleCat.of ℂ ℂ)) p q n h
      (RationalSmoothCech.CM.Construction.rationalSmoothCechCoefficients E M U p q c) :=
  ConcreteCategory.congr_hom (RationalTotalMap.CM.Construction.rationalComplexTotalDegreeMap_iota
    (DivisorClass.Chern.Rational.CechComparison.RationalCech.singularCechDoubleComplex (TopCat.of M) U (ModuleCat.of ℚ ℚ))
    (AlgebraicTopology.Cohomology.Singular.SmoothCechDoubleComplex.manifoldSmoothCechDoubleComplex E M U (ModuleCat.of ℂ ℂ))
    (rationalSmoothCechComponent E M U) p q n h) c

end

/-! The rational-to-smooth total map intertwines the actual global
singular and smooth Čech augmentations. -/

open _root_.CategoryTheory _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

variable (E M : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] {I : Type} (U : I → Opens M)

theorem rationalSmoothCechCoefficients_global (n : ℕ)
    (c : (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℚ ℚ) (TopCat.of M)).X n) :
    RationalSmoothCech.CM.Construction.rationalSmoothCechCoefficients E M U 0 n
      ((DivisorClass.Chern.Rational.CechComparison.RationalCech.globalSingularCechColumnAugmentation
        (TopCat.of M) U (ModuleCat.of ℚ ℚ)).f n c) =
      (AlgebraicTopology.Cohomology.Singular.SmoothCechDoubleComplex.globalManifoldSmoothCechColumnAugmentation E M U (ModuleCat.of ℂ ℂ)).f n
        (RationalSmoothCochains.CM.Construction.rationalSmoothCochain E M n c) := by
  funext a
  have hQ := DivisorClass.Chern.Rational.CechComparison.RationalCech.globalSingularCechColumnAugmentation_apply
    (TopCat.of M) U (ModuleCat.of ℚ ℚ) n c a
  have hC := AlgebraicTopology.Cohomology.Singular.SmoothCechDoubleComplex.globalManifoldSmoothCechColumnAugmentation_apply E M U (ModuleCat.of ℂ ℂ)
    n (RationalSmoothCochains.CM.Construction.rationalSmoothCochain E M n c) a
  exact (congrArg (RationalSmoothCochains.CM.Construction.rationalSmoothCochain E (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a) n) hQ).trans
    ((RationalSmoothCochains.CM.Construction.rationalSmoothCochain_pullback (Subtype.val : AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a → M)
      (contMDiff_subtype_val (I := 𝓘(ℝ, E)) (n := ∞)) n c).symm.trans hC.symm)

theorem rationalSmoothCechTotalMap_global_apply (n : ℕ)
    (c : (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℚ ℚ) (TopCat.of M)).X n) :
    (rationalSmoothCechTotalMap E M U).f n
      ((DivisorClass.Chern.Rational.CechComparison.RationalCech.globalSingularCechAugmentation
        (TopCat.of M) U (ModuleCat.of ℚ ℚ)).f n c) =
      (AlgebraicTopology.Cohomology.Singular.SmoothCechDoubleComplex.globalManifoldSmoothCechAugmentation E M U (ModuleCat.of ℂ ℂ)).f n
        (RationalSmoothCochains.CM.Construction.rationalSmoothCochain E M n c) := by
  have hQ := ConcreteCategory.congr_hom
    (DivisorClass.Chern.Rational.CechComparison.RationalCech.globalSingularCechAugmentation_f (TopCat.of M) U (ModuleCat.of ℚ ℚ) n) c
  have hC := ConcreteCategory.congr_hom
    (AlgebraicTopology.Cohomology.Singular.SmoothCechDoubleComplex.globalManifoldSmoothCechAugmentation_f E M U (ModuleCat.of ℂ ℂ) n) (RationalSmoothCochains.CM.Construction.rationalSmoothCochain E M n c)
  let T : (DivisorClass.Chern.Rational.CechComparison.RationalCech.singularCechTotal (TopCat.of M) U (ModuleCat.of ℚ ℚ)).X n →
      (AlgebraicTopology.Cohomology.Singular.SmoothCechDoubleComplex.manifoldSmoothCechTotal E M U (ModuleCat.of ℂ ℂ)).X n := (rationalSmoothCechTotalMap E M U).f n
  let cq : RationalSmoothCech.CM.Construction.RationalSingularCechSections M U 0 n :=
    (DivisorClass.Chern.Rational.CechComparison.RationalCech.globalSingularCechColumnAugmentation (TopCat.of M) U (ModuleCat.of ℚ ℚ)).f n c
  let cs : RationalSmoothCech.CM.Construction.ComplexSmoothCechSections E M U 0 n :=
    (AlgebraicTopology.Cohomology.Singular.SmoothCechDoubleComplex.globalManifoldSmoothCechColumnAugmentation E M U (ModuleCat.of ℂ ℂ)).f n (RationalSmoothCochains.CM.Construction.rationalSmoothCochain E M n c)
  let iQ := DivisorClass.Chern.Rational.Cech.RationalCech.cechTotalInclusion U
    (AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularPresheafComplex (ModuleCat.of ℚ ℚ) (TopCat.of M)) 0 n n (Nat.zero_add n)
  let iC := AlgebraicTopology.DeRham.Comparison.CechTotalFunctor.cechTotalInclusion U (AlgebraicTopology.Cohomology.Singular.ManifoldSmoothPresheaf.manifoldSmoothPresheafComplex E M (ModuleCat.of ℂ ℂ)) 0 n n (Nat.zero_add n)
  have h₁ : T ((DivisorClass.Chern.Rational.CechComparison.RationalCech.globalSingularCechAugmentation
      (TopCat.of M) U (ModuleCat.of ℚ ℚ)).f n c) = T (iQ cq) := congrArg T hQ
  have h₂ : T (iQ cq) = iC (RationalSmoothCech.CM.Construction.rationalSmoothCechCoefficients E M U 0 n cq) :=
    rationalSmoothCechTotalMap_iota E M U 0 n n (Nat.zero_add n) cq
  have h₃ : iC (RationalSmoothCech.CM.Construction.rationalSmoothCechCoefficients E M U 0 n cq) = iC cs :=
    congrArg iC (rationalSmoothCechCoefficients_global E M U n c)
  exact h₁.trans (h₂.trans (h₃.trans hC.symm))

theorem rationalSmoothCechTotalMap_global :
    DivisorClass.Chern.Rational.CechComparison.RationalCech.globalSingularCechAugmentation (TopCat.of M) U (ModuleCat.of ℚ ℚ) ≫
      rationalSmoothCechTotalMap E M U =
    RationalSmoothCech.CM.Construction.rationalSmoothCochainMap E M ≫
      (PositiveCohomologyConjugation.CM.Construction.restrictToRational.mapHomologicalComplex (ComplexShape.up ℕ)).map
        (AlgebraicTopology.Cohomology.Singular.SmoothCechDoubleComplex.globalManifoldSmoothCechAugmentation E M U (ModuleCat.of ℂ ℂ)) := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro c
  exact rationalSmoothCechTotalMap_global_apply E M U n c

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.RationalSmoothCechAugmentation.CM.Construction
