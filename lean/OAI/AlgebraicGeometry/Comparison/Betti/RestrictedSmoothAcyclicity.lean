import OAI.AlgebraicGeometry.Comparison.Betti.RestrictedSmoothGodementExactness
import OAI.AlgebraicGeometry.Comparison.Betti.Godement.Injective
import OAI.AlgebraicGeometry.Comparison.Betti.ConstantSheafSections
import OAI.AlgebraicGeometry.Comparison.Betti.InjectiveHomologyExt

/-! # Restricted Smooth Acyclicity -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.RestrictedSmoothAcyclicity.Godement

noncomputable section

/-! Literal restrictions of the ambient smooth form sheaves are acyclic on sigma-compact open submanifolds. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.Abelian _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]

local instance (O : Opens M) : HasExt.{1} (ConstantSheafSections.ComplexSheaves (TopCat.of O)) := HasExt.standard _

theorem restrictedSmoothFormInjective_sections_exactAt_succ (O : Opens M) [SigmaCompactSpace O]
    (p n : ℕ) :
    (((FlasqueBiproduct.sections (⊤ : Opens O)).mapHomologicalComplex (.up ℕ)).obj
      (injectiveResolution (RestrictedSmoothSheaf.Godement.restrictedSmoothFormSheaf E M O p)).cocomplex).ExactAt (n + 1) := by
  let F := RestrictedSmoothSheaf.Godement.restrictedSmoothFormSheaf E M O p
  have hq := Godement.Injective.godementToInjective_sections_quasiIso F ⊤
  let f := ((FlasqueBiproduct.sections (⊤ : Opens O)).mapHomologicalComplex (.up ℕ)).map (Godement.Injective.godementToInjective F)
  have hf : QuasiIso f := hq
  apply (HomologicalComplex.exactAt_iff_isZero_homology _ _).mpr
  exact ((RestrictedSmoothGodementExactness.restrictedSmoothFormGodement_sections_exactAt_succ (E := E) O p n).isZero_homology).of_iso
    (isoOfQuasiIsoAt f (n + 1)).symm

theorem restrictedSmoothFormSheaf_ext_vanish (O : Opens M) [SigmaCompactSpace O] (p q : ℕ) :
    Subsingleton (Ext.{1} (ConstantSheafSections.standardConstantSheaf (TopCat.of O))
      (RestrictedSmoothSheaf.Godement.restrictedSmoothFormSheaf E M O p) (q + 1)) := by
  let I : InjectiveResolution
      (show ConstantSheafSections.ComplexSheaves (TopCat.of O) from RestrictedSmoothSheaf.Godement.restrictedSmoothFormSheaf E M O p) :=
    injectiveResolution (RestrictedSmoothSheaf.Godement.restrictedSmoothFormSheaf E M O p)
  have h := (restrictedSmoothFormInjective_sections_exactAt_succ (E := E) O p q).of_iso
    (ConstantSheafSections.constantHomSectionsComplexIso I.cocomplex).symm
  have hz : IsZero ((InjectiveHomologyExt.homSectionsComplex (C := ConstantSheafSections.ComplexSheaves (TopCat.of O)) (R := ℂ) I
      (ConstantSheafSections.standardConstantSheaf (TopCat.of O))).homology (q + 1)) := h.isZero_homology
  have : Subsingleton ((InjectiveHomologyExt.homSectionsComplex (C := ConstantSheafSections.ComplexSheaves (TopCat.of O)) (R := ℂ) I
      (ConstantSheafSections.standardConstantSheaf (TopCat.of O))).homology (q + 1)) := ModuleCat.subsingleton_of_isZero hz
  exact (InjectiveHomologyExt.homologyExtLinearEquiv (C := ConstantSheafSections.ComplexSheaves (TopCat.of O)) (R := ℂ)
    (X := ConstantSheafSections.standardConstantSheaf (TopCat.of O)) I (q + 1)).symm.injective.subsingleton

end

end OAI.AlgebraicGeometry.Comparison.Betti.RestrictedSmoothAcyclicity.Godement
