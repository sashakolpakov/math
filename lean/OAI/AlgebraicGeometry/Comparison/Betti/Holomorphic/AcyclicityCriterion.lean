import OAI.AlgebraicGeometry.Comparison.Betti.Complex.AntiResolution
import OAI.AlgebraicGeometry.Comparison.Betti.SigmaCompactAntiAcyclicity
import OAI.AlgebraicGeometry.Comparison.Betti.Acyclic.ResolutionExtCalculation
import OAI.AlgebraicGeometry.Comparison.Betti.Complex.SheafCohomology

/-! # Acyclicity Criterion -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.AcyclicityCriterion.Dolbeault

noncomputable section

/-! Global primitives in the actual Dolbeault resolution imply higher
cohomology vanishing for the native holomorphic function sheaf. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.Abelian _root_.TopologicalSpace _root_.HomologicalComplex
open scoped _root_.Manifold ContDiff

attribute [local instance] Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

variable (E M : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
  [IsScalarTower ℝ ℂ E] [FiniteDimensional ℂ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ∞ M]

omit [FiniteDimensional ℂ E] in
theorem antiDolbeault_sections_exact_of_primitive (q : ℕ)
    (h : ∀ a : DivisorClass.Chern.Open.ManifoldBidegree.AntiOpenManifoldForm E (⊤ : Opens M) (q + 1),
      DivisorClass.Chern.Manifold.DolbeaultCharts.pureOpenManifoldDolbeaultD (⊤ : Opens M) (q + 1) a = 0 →
      ∃ t : DivisorClass.Chern.Open.ManifoldBidegree.AntiOpenManifoldForm E (⊤ : Opens M) q,
        DivisorClass.Chern.Manifold.DolbeaultCharts.pureOpenManifoldDolbeaultD (⊤ : Opens M) q t = a) :
    (((FlasqueBiproduct.sections (⊤ : Opens M)).mapHomologicalComplex (.up ℕ)).obj
      (Complex.AntiDolbeault.complexAntiDolbeaultComplex E M)).ExactAt (q + 1) := by
  apply (HomologicalComplex.exactAt_iff' _ q (q + 1) (q + 1 + 1) (by simp) (by simp)).mpr
  rw [ShortComplex.moduleCat_exact_iff]
  simp only [HomologicalComplex.sc', shortComplexFunctor', Functor.mapHomologicalComplex_obj_d,
    Complex.AntiDolbeault.complexAntiDolbeaultComplex, CochainComplex.of_d]
  exact h

variable [SigmaCompactSpace M] [T2Space M]

local instance : HasExt.{1} (ConstantSheafSections.ComplexSheaves (TopCat.of M)) := HasExt.standard _

theorem holomorphicScalarSheaf_ext_vanish_of_primitives
    (h : ∀ q, ∀ a : DivisorClass.Chern.Open.ManifoldBidegree.AntiOpenManifoldForm E (⊤ : Opens M) (q + 1),
      DivisorClass.Chern.Manifold.DolbeaultCharts.pureOpenManifoldDolbeaultD (⊤ : Opens M) (q + 1) a = 0 →
      ∃ t : DivisorClass.Chern.Open.ManifoldBidegree.AntiOpenManifoldForm E (⊤ : Opens M) q,
        DivisorClass.Chern.Manifold.DolbeaultCharts.pureOpenManifoldDolbeaultD (⊤ : Opens M) q t = a) (q : ℕ) :
    Subsingleton (Ext.{1} (ConstantSheafSections.standardConstantSheaf (TopCat.of M))
      (ScalarSheaf.Dolbeault.holomorphicScalarSheaf E M) (q + 1)) := by
  have : FiniteDimensional ℝ E := FiniteDimensional.trans ℝ ℂ E
  let D := Complex.AntiResolution.Dolbeault.complexAntiDolbeaultResolution E M
  have hExt (p n : ℕ) : Subsingleton
      (Ext.{1} (ConstantSheafSections.standardConstantSheaf (TopCat.of M)) (D.complex.X p) (n + 1)) :=
    SigmaCompactAntiAcyclicity.Dolbeault.sigmaCompact_antiFormSheaf_ext_vanish E M p n
  let hAb : Abelian (ConstantSheafSections.ComplexSheaves (TopCat.of M)) := inferInstance
  have hI : EnoughInjectives (ConstantSheafSections.ComplexSheaves (TopCat.of M)) := inferInstance
  let hEx : HasExt.{1} (ConstantSheafSections.ComplexSheaves (TopCat.of M)) := HasExt.standard _
  refine @Acyclic.ResolutionExtCalculation.acyclicResolution_ext_vanish
    (ConstantSheafSections.ComplexSheaves (TopCat.of M)) _ hAb hI hEx ℂ _ _
    (ConstantSheafSections.standardConstantSheaf (TopCat.of M)) _ D hExt ?_ q
  intro n
  exact (antiDolbeault_sections_exact_of_primitive E M n (h n)).of_iso
    (ConstantSheafSections.constantHomSectionsComplexIso D.complex).symm

theorem holomorphicFunctionSheaf_cohomology_vanish_of_primitives
    (h : ∀ q, ∀ a : DivisorClass.Chern.Open.ManifoldBidegree.AntiOpenManifoldForm E (⊤ : Opens M) (q + 1),
      DivisorClass.Chern.Manifold.DolbeaultCharts.pureOpenManifoldDolbeaultD (⊤ : Opens M) (q + 1) a = 0 →
      ∃ t : DivisorClass.Chern.Open.ManifoldBidegree.AntiOpenManifoldForm E (⊤ : Opens M) q,
        DivisorClass.Chern.Manifold.DolbeaultCharts.pureOpenManifoldDolbeaultD (⊤ : Opens M) q t = a) (q : ℕ) :
    Subsingleton (Sheaf.H.{0} (DivisorClass.Chern.Holomorphic.Sheaves.holomorphicFunctionSheaf E M) (q + 1)) := by
  have := holomorphicScalarSheaf_ext_vanish_of_primitives E M h q
  obtain ⟨e, _⟩ := Complex.SheafCohomology.complexSheafCohomologyForgetEquiv (TopCat.of M)
    (ScalarSheaf.Dolbeault.holomorphicScalarSheaf E M) (q + 1)
  exact e.symm.injective.subsingleton

end

end OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.AcyclicityCriterion.Dolbeault
