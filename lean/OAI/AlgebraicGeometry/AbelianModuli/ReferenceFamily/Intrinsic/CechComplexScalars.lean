import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.CechDifferential
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Cech.GlobalScalarCoordinates
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Holomorphic.Scalars

/-! # Cech Complex Scalars -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.CechComplexScalars

noncomputable section

/-! Native evaluation of the specified complex-base constants agrees
with ordinary complex multiplication on literal holomorphic Cech cochains. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

variable (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)

theorem complexGlobalScalars_nativeValue (c : ℂ) (x : A.variety.analyticSpace) :
    RepresentationTheory.Theta.Geometric.Complex.SectionEvaluation.complexSectionValue x.left ⊤ (by trivial) (SheafCohomology.Sheaves.Projective.complexGlobalScalars A c) = c := by
  have h := RepresentationTheory.Theta.Geometric.Complex.SectionEvaluation.complexSectionValue_pullback x.left A.variety.structureMap ⊤ ⊤
    (by intro y _; trivial) (by trivial) ((Scheme.ΓSpecIso (.of ℂ)).inv c)
  have ht : A.variety.structureMap.appLE ⊤ ⊤ (by intro y _; trivial) = A.variety.structureMap.appTop :=
    A.variety.structureMap.appLE_eq_app
  erw [ht] at h
  have hw : x.left ≫ A.variety.structureMap = 𝟙 Foundations.Scheme.ProjectiveSpace.complexBase := x.w
  have he := RepresentationTheory.Theta.Geometric.Complex.SectionEvaluation.complexSectionValue_congr (x.left ≫ A.variety.structureMap) (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase)
    hw ⊤ (by trivial) (by trivial) ((Scheme.ΓSpecIso (.of ℂ)).inv c)
  refine h.trans (he.trans ?_)
  change (Scheme.ΓSpecIso (.of ℂ)).hom (Scheme.Hom.appTop (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase) ((Scheme.ΓSpecIso (.of ℂ)).inv c)) = c
  rw [Scheme.Hom.id_appTop]
  exact (Scheme.ΓSpecIso (.of ℂ)).inv_hom_id_apply c

variable {I : Type} (U : I → A.carrier.Opens)

theorem nativeCechCochain_complexScalar (n : ℕ) (c : ℂ)
    (z : Γ(Cech.TermModules.cechTermModule A.carrier U n, ⊤)) :
    CechDifferential.nativeCechCochain A.variety U n (SheafCohomology.Sheaves.Projective.complexGlobalScalars A c • z) =
      DivisorClass.Chern.Abelian.CechClasses.abelianCechCoefficient (X := TopCat.of A.variety.analyticSpace) (CechDifferential.nativeCechCover A.variety U)
        (RepresentationTheory.Theta.Geometric.Holomorphic.PicardPeriodQuotient.holomorphicScalarSheafMap A.variety.analyticModel A.variety.analyticSpace c).hom n
        (CechDifferential.nativeCechCochain A.variety U n z) := by
  funext i
  change CechDifferential.nativeCechFunction A.variety U n (SheafCohomology.Sheaves.Projective.complexGlobalScalars A c • z) i =
    c • CechDifferential.nativeCechFunction A.variety U n z i
  apply DFunLike.ext
  intro x
  change CechDifferential.nativeCechFunction A.variety U n (SheafCohomology.Sheaves.Projective.complexGlobalScalars A c • z) i x =
    c * CechDifferential.nativeCechFunction A.variety U n z i x
  rw [CechDifferential.nativeCechCochain_value, CechDifferential.nativeCechCochain_value]
  erw [CechDifferential.nativeCechValue_smul, complexGlobalScalars_nativeValue]

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.CechComplexScalars
