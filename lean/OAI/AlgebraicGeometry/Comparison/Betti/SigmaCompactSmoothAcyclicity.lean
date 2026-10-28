import OAI.AlgebraicGeometry.Comparison.Betti.SigmaCompactGodementExactness
import OAI.AlgebraicGeometry.Comparison.Betti.Godement.Injective
import OAI.AlgebraicGeometry.Comparison.Betti.ConstantSheafSections
import OAI.AlgebraicGeometry.Comparison.Betti.InjectiveHomologyExt

/-! # Sigma Compact Smooth Acyclicity -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.SigmaCompactSmoothAcyclicity.Godement

noncomputable section

/-! The actual smooth form sheaves on a sigma-compact manifold have no higher
Ext from the constant complex sheaf. This is proved via their Godement resolution. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.Abelian _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

variable (E M : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [SigmaCompactSpace M] [T2Space M]

local instance : HasExt.{1} (ConstantSheafSections.ComplexSheaves (TopCat.of M)) := HasExt.standard _

theorem sigmaCompact_smoothFormGodement_sections_exactAt_succ (p n : ℕ) :
    (((FlasqueBiproduct.sections (⊤ : Opens M)).mapHomologicalComplex (.up ℕ)).obj
      (Godement.Resolution.godementComplex (TopCat.of M) (Analysis.DifferentialForms.Manifold.ManifoldSheaf.manifoldFormSheaf E M p))).ExactAt (n + 1) := by
  apply (HomologicalComplex.exactAt_iff' _ n (n + 1) (n + 2) (by simp) (by simp)).mpr
  rw [ShortComplex.moduleCat_exact_iff]
  exact SigmaCompactGodementExactness.sigmaCompact_smoothFormGodement_global_lift E M p n

theorem sigmaCompact_smoothFormInjective_sections_exactAt_succ (p n : ℕ) :
    (((FlasqueBiproduct.sections (⊤ : Opens M)).mapHomologicalComplex (.up ℕ)).obj
      (injectiveResolution (Analysis.DifferentialForms.Manifold.ManifoldSheaf.manifoldFormSheaf E M p)).cocomplex).ExactAt (n + 1) := by
  have hq := Godement.Injective.godementToInjective_sections_quasiIso (Analysis.DifferentialForms.Manifold.ManifoldSheaf.manifoldFormSheaf E M p) ⊤
  let f := ((FlasqueBiproduct.sections (⊤ : Opens M)).mapHomologicalComplex (.up ℕ)).map
    (Godement.Injective.godementToInjective (Analysis.DifferentialForms.Manifold.ManifoldSheaf.manifoldFormSheaf E M p))
  have hf : QuasiIso f := hq
  apply (HomologicalComplex.exactAt_iff_isZero_homology _ _).mpr
  exact ((sigmaCompact_smoothFormGodement_sections_exactAt_succ E M p n).isZero_homology).of_iso
    (isoOfQuasiIsoAt f (n + 1)).symm

theorem sigmaCompact_smoothFormSheaf_ext_vanish (p q : ℕ) :
    Subsingleton (Ext.{1} (ConstantSheafSections.standardConstantSheaf (TopCat.of M))
      (Analysis.DifferentialForms.Manifold.ManifoldSheaf.manifoldFormSheaf E M p) (q + 1)) := by
  let I : InjectiveResolution (show ConstantSheafSections.ComplexSheaves (TopCat.of M) from Analysis.DifferentialForms.Manifold.ManifoldSheaf.manifoldFormSheaf E M p) :=
    injectiveResolution (Analysis.DifferentialForms.Manifold.ManifoldSheaf.manifoldFormSheaf E M p)
  have h := (sigmaCompact_smoothFormInjective_sections_exactAt_succ E M p q).of_iso
    (ConstantSheafSections.constantHomSectionsComplexIso I.cocomplex).symm
  have hz : IsZero ((InjectiveHomologyExt.homSectionsComplex (C := ConstantSheafSections.ComplexSheaves (TopCat.of M)) (R := ℂ) I
      (ConstantSheafSections.standardConstantSheaf (TopCat.of M))).homology (q + 1)) := h.isZero_homology
  have : Subsingleton ((InjectiveHomologyExt.homSectionsComplex (C := ConstantSheafSections.ComplexSheaves (TopCat.of M)) (R := ℂ) I
      (ConstantSheafSections.standardConstantSheaf (TopCat.of M))).homology (q + 1)) :=
    ModuleCat.subsingleton_of_isZero hz
  exact (InjectiveHomologyExt.homologyExtLinearEquiv (C := ConstantSheafSections.ComplexSheaves (TopCat.of M)) (R := ℂ)
    (X := ConstantSheafSections.standardConstantSheaf (TopCat.of M)) I (q + 1)).symm.injective.subsingleton

end

end OAI.AlgebraicGeometry.Comparison.Betti.SigmaCompactSmoothAcyclicity.Godement
