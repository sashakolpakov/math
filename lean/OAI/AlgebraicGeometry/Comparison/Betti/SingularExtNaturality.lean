import OAI.AlgebraicGeometry.Comparison.Betti.InjectiveExtPullback
import OAI.AlgebraicGeometry.Comparison.Betti.SingularInjectiveNaturality

/-! # Singular Ext Naturality -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.SingularExtNaturality

noncomputable section

/-! Naturality of the actual singular-cohomology-to-Ext equivalence. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.Abelian _root_.TopologicalSpace

variable (M : TopCat.{0}) [StronglyLocallyContractibleSpace M] [MetrizableSpace M]

def singularLocallyConstantExtEquiv (n : ℕ) :
    AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℂ ℂ) M n ≃ₗ[ℂ]
      Ext.{1} (ConstantSheafSections.standardConstantSheaf M) (InjectiveExtPullback.locallyConstantCoefficients M) n :=
  (SingularInjective.singularInjectiveSectionsCohomologyIso M n).toLinearEquiv.trans
    (((HomologicalComplex.homologyFunctor (ModuleCat.{0} ℂ) (ComplexShape.up ℕ) n).mapIso
      (InjectiveHomPullback.injectiveHomSectionsIso M).symm).toLinearEquiv.trans (InjectiveExtPullback.injectiveHomologyExtEquiv M n))

variable {M} {N : TopCat.{0}} [StronglyLocallyContractibleSpace N] [MetrizableSpace N] (f : M ⟶ N)

theorem singularLocallyConstantExtEquiv_naturality (n : ℕ)
    (a : AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℂ ℂ) N n) :
    singularLocallyConstantExtEquiv M n
        (HomologicalComplex.homologyMap (AlgebraicTopology.Cohomology.Singular.Functor.singularPullback (ModuleCat.of ℂ ℂ) f) n a) =
      InjectiveExtPullback.locallyConstantExtPullback f n (singularLocallyConstantExtEquiv N n a) := by
  let H := HomologicalComplex.homologyFunctor (ModuleCat.{0} ℂ) (ComplexShape.up ℕ) n
  have h₁ := ConcreteCategory.congr_hom (SingularInjectiveNaturality.singularToInjectiveSections_homology_naturality f n) a
  have h₂ : H.map (TopologicalSheafPullback.injectiveSectionsPullback f) ≫ H.map (InjectiveHomPullback.injectiveHomSectionsIso M).inv =
      H.map (InjectiveHomPullback.injectiveHomSectionsIso N).inv ≫ H.map (InjectiveHomPullback.injectiveHomSectionsPullback f) :=
    (H.map_comp (TopologicalSheafPullback.injectiveSectionsPullback f) (InjectiveHomPullback.injectiveHomSectionsIso M).inv).symm.trans
      ((H.congr_map (InjectiveHomPullback.injectiveHomSectionsPullback_sections f)).trans
        (H.map_comp (InjectiveHomPullback.injectiveHomSectionsIso N).inv (InjectiveHomPullback.injectiveHomSectionsPullback f)))
  have h₃ := ConcreteCategory.congr_hom h₂ (H.map (SingularInjective.singularToInjectiveSections N) a)
  change InjectiveExtPullback.injectiveHomologyExtEquiv M n
    (H.map (InjectiveHomPullback.injectiveHomSectionsIso M).inv
      (H.map (SingularInjective.singularToInjectiveSections M) (H.map (AlgebraicTopology.Cohomology.Singular.Functor.singularPullback (ModuleCat.of ℂ ℂ) f) a))) = _
  change H.map (SingularInjective.singularToInjectiveSections M) (H.map (AlgebraicTopology.Cohomology.Singular.Functor.singularPullback (ModuleCat.of ℂ ℂ) f) a) =
    H.map (TopologicalSheafPullback.injectiveSectionsPullback f) (H.map (SingularInjective.singularToInjectiveSections N) a) at h₁
  rw [h₁]
  change H.map (InjectiveHomPullback.injectiveHomSectionsIso M).inv
      (H.map (TopologicalSheafPullback.injectiveSectionsPullback f) (H.map (SingularInjective.singularToInjectiveSections N) a)) =
    H.map (InjectiveHomPullback.injectiveHomSectionsPullback f)
      (H.map (InjectiveHomPullback.injectiveHomSectionsIso N).inv (H.map (SingularInjective.singularToInjectiveSections N) a)) at h₃
  rw [h₃]
  exact InjectiveExtPullback.injectiveHomologyExtEquiv_pullback f n _

end

end OAI.AlgebraicGeometry.Comparison.Betti.SingularExtNaturality
