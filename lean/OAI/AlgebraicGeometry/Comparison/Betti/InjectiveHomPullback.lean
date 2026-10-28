import OAI.AlgebraicGeometry.Comparison.Betti.SectionsPullbackNormalization
import OAI.AlgebraicGeometry.Comparison.Betti.HomologyExtNaturality
import OAI.AlgebraicGeometry.Comparison.Betti.Derived.DerivedSheafBetti

/-! # Injective Hom Pullback -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.InjectiveHomPullback

noncomputable section

/-! Pullback on actual Hom complexes has the expected coefficient formula. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite

abbrev injectiveHomSectionsComplex (M : TopCat.{0}) : CochainComplex (ModuleCat.{0} ℂ) ℕ :=
  InjectiveHomologyExt.homSectionsComplex (C := ConstantSheafSections.ComplexSheaves M) (R := ℂ)
    (SingularInjective.singularInjectiveResolution M) (ConstantSheafSections.standardConstantSheaf M)

def injectiveHomSectionsIso (M : TopCat.{0}) : injectiveHomSectionsComplex M ≅
    ((TopologicalSheafPullback.globalSections M).mapHomologicalComplex (ComplexShape.up ℕ)).obj
      (SingularInjective.singularInjectiveResolution M).cocomplex :=
  ConstantSheafSections.constantHomSectionsComplexIso
    (show CochainComplex (ConstantSheafSections.ComplexSheaves M) ℕ from (SingularInjective.singularInjectiveResolution M).cocomplex)

variable {M N : TopCat.{0}} (f : M ⟶ N)

def injectiveHomSectionsPullback : injectiveHomSectionsComplex N ⟶ injectiveHomSectionsComplex M :=
  (injectiveHomSectionsIso N).hom ≫ TopologicalSheafPullback.injectiveSectionsPullback f ≫ (injectiveHomSectionsIso M).inv

theorem injectiveHomSectionsPullback_f (n : ℕ)
    (g : ConstantSheafSections.standardConstantSheaf N ⟶
      (show CochainComplex (ConstantSheafSections.ComplexSheaves N) ℕ from (SingularInjective.singularInjectiveResolution N).cocomplex).X n) :
    (injectiveHomSectionsPullback f).f n g =
      ((TopologicalSheafPullback.constantPullbackIso f).inv ≫ (TopologicalSheafPullback.sheafInverseImage f).map g) ≫
        (TopologicalSheafPullback.injectiveResolutionPullback f).f n := by
  let A : ConstantSheafSections.ComplexSheaves N := (SingularInjective.singularInjectiveResolution N).cocomplex.X n
  let B : ConstantSheafSections.ComplexSheaves M := (SingularInjective.singularInjectiveResolution M).cocomplex.X n
  let p : (TopologicalSheafPullback.sheafInverseImage f).obj A ⟶ B := (TopologicalSheafPullback.injectiveResolutionPullback f).f n
  have h₁ := ConstantSheafSections.constantHomSectionsLinearEquiv_symm_naturality
    ((TopologicalSheafPullback.globalSectionPullback f).app A (ConstantSheafSections.constantHomSectionsLinearEquiv A g)) p
  have h₂ := SectionsPullbackNormalization.constantHomSectionsLinearEquiv_symm_pullback f A (ConstantSheafSections.constantHomSectionsLinearEquiv A g)
  erw [(ConstantSheafSections.constantHomSectionsLinearEquiv A).symm_apply_apply g] at h₂
  exact h₁.symm.trans (congrArg (fun k => k ≫ p) h₂)

theorem injectiveHomSectionsPullback_sections :
    TopologicalSheafPullback.injectiveSectionsPullback f ≫ (injectiveHomSectionsIso M).inv =
      (injectiveHomSectionsIso N).inv ≫ injectiveHomSectionsPullback f := by
  change _ = (injectiveHomSectionsIso N).inv ≫
    ((injectiveHomSectionsIso N).hom ≫ TopologicalSheafPullback.injectiveSectionsPullback f ≫ (injectiveHomSectionsIso M).inv)
  exact ((injectiveHomSectionsIso N).inv_hom_id_assoc _).symm

end

end OAI.AlgebraicGeometry.Comparison.Betti.InjectiveHomPullback
