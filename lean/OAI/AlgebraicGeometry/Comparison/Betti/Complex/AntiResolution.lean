import OAI.AlgebraicGeometry.Comparison.Betti.Complex.AntiDolbeault
import OAI.AlgebraicGeometry.Comparison.Betti.AntiFormExtVanishing

/-! # Anti Resolution -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Complex.AntiResolution.Dolbeault

noncomputable section

/-! The complex-linear Dolbeault resolution of the native holomorphic
function sheaf, with proved acyclic terms on compact complex manifolds. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.Abelian _root_.TopologicalSpace _root_.HomologicalComplex
open scoped _root_.Manifold ContDiff

attribute [local instance] Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

variable (E M : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
  [IsScalarTower ℝ ℂ E] [FiniteDimensional ℂ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ∞ M]

theorem complexAntiDolbeaultComplex_exactAt_succ (q : ℕ) :
    (AntiDolbeault.complexAntiDolbeaultComplex E M).ExactAt (q + 1) := by
  apply (HomologicalComplex.exactAt_iff' _ q (q + 1) (q + 1 + 1) (by simp) (by simp)).mpr
  simpa only [AntiDolbeault.complexAntiDolbeaultSequence, HomologicalComplex.sc', shortComplexFunctor',
    AntiDolbeault.complexAntiDolbeaultComplex, CochainComplex.of_d] using
    AntiDolbeault.complexAntiDolbeaultSequence_exact E M q

def complexAntiDolbeaultResolution : ResolutionExactImage.Data (Holomorphic.ScalarSheaf.Dolbeault.holomorphicScalarSheaf E M) where
  complex := AntiDolbeault.complexAntiDolbeaultComplex E M
  augmentation := AntiDolbeault.holomorphicToComplexAntiZero E M
  augmentation_d := AntiDolbeault.holomorphicToComplexAntiZero_d E M
  isKernel := by
    let S := AntiDolbeault.holomorphicComplexAntiZeroSequence E M
    have : Balanced (TopCat.Sheaf (ModuleCat.{0} ℂ) (TopCat.of M)) :=
      inferInstanceAs (Balanced (Sheaf (Opens.grothendieckTopology (TopCat.of M)) (ModuleCat.{0} ℂ)))
    have : Mono S.f := AntiDolbeault.holomorphicToComplexAntiZero_mono E M
    exact (AntiDolbeault.holomorphicComplexAntiZeroSequence_exact E M).fIsKernel
  exact_succ := complexAntiDolbeaultComplex_exactAt_succ E M

def holomorphicComplexAntiAugmentation :
    (CochainComplex.single₀ (TopCat.Sheaf (ModuleCat.{0} ℂ) (TopCat.of M))).obj
      (Holomorphic.ScalarSheaf.Dolbeault.holomorphicScalarSheaf E M) ⟶ AntiDolbeault.complexAntiDolbeaultComplex E M :=
  ResolutionExactImage.cochainAugmentation (complexAntiDolbeaultResolution E M)

instance complexAntiDolbeaultComplex_hasHomology (n : ℕ) :
    HasHomology (AntiDolbeault.complexAntiDolbeaultComplex E M) n := by
  change HasHomology (complexAntiDolbeaultResolution E M).complex n
  infer_instance

theorem holomorphicComplexAntiAugmentation_quasiIso :
    QuasiIso (holomorphicComplexAntiAugmentation E M) :=
  ResolutionExactImage.cochainAugmentation_quasiIso (complexAntiDolbeaultResolution E M)

local instance : HasExt.{1} (ConstantSheafSections.ComplexSheaves (TopCat.of M)) := HasExt.standard _

theorem complexAntiDolbeaultComplex_term_ext_vanish [CompactSpace M] [T2Space M] (p q : ℕ) :
    Subsingleton (Ext.{1} (ConstantSheafSections.standardConstantSheaf (TopCat.of M))
      ((AntiDolbeault.complexAntiDolbeaultComplex E M).X p) (q + 1)) := by
  have : FiniteDimensional ℝ E := FiniteDimensional.trans ℝ ℂ E
  exact AntiFormExtVanishing.Dolbeault.antiFormSheaf_ext_vanish E M p q

end

end OAI.AlgebraicGeometry.Comparison.Betti.Complex.AntiResolution.Dolbeault
