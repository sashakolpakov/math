import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.CechClassScalars
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Cech.ClassCoefficientNaturality

/-! # Analytification Scalars -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Cech.AnalytificationScalars

noncomputable section

section

/-! Native classes of scalar-multiplied algebraic cocycles use the
canonical scalar action of the holomorphic coefficient sheaf. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

variable (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) {I : Type} (U : I → A.carrier.Opens) (hU : iSup U = ⊤)

theorem nativeCechOneClass_scalar (c : ℂ) (z : Γ(TermModules.cechTermModule A.carrier U 1, ⊤))
    (hz : (ModuleDifferential.cechModuleDifferential A.carrier U 1).app ⊤ z = 0) :
    Intrinsic.CechBoundaryReflection.nativeCechOneClass A.variety U hU (SheafCohomology.Sheaves.Projective.complexGlobalScalars A c • z)
      (CechClassScalars.algebraicCech_closed_smul A U _ z hz) =
        RepresentationTheory.Theta.Geometric.Holomorphic.PicardPeriodQuotient.holomorphicScalarH1 A.variety.analyticModel A.variety.analyticSpace c
          (Intrinsic.CechBoundaryReflection.nativeCechOneClass A.variety U hU z hz) := by
  exact ClassCoefficientNaturality.cechSheafClass_eq_map_of_coefficient (X := TopCat.of A.variety.analyticSpace)
    (Intrinsic.CechDifferential.nativeCechCover A.variety U)
    (RepresentationTheory.Theta.Geometric.Holomorphic.PicardPeriodQuotient.holomorphicScalarSheafMap A.variety.analyticModel A.variety.analyticSpace c)
    (Intrinsic.CechDifferential.nativeCechCover_covers A.variety U hU) 0 (Intrinsic.CechDifferential.nativeCechCochain A.variety U 1 z)
    (Intrinsic.CechDifferential.nativeCechCochain A.variety U 1 (SheafCohomology.Sheaves.Projective.complexGlobalScalars A c • z))
    (Intrinsic.CechDifferential.nativeCechCochain_closed A.variety U 1 z hz)
    (Intrinsic.CechDifferential.nativeCechCochain_closed A.variety U 1 _ (CechClassScalars.algebraicCech_closed_smul A U _ z hz))
    (Intrinsic.CechComplexScalars.nativeCechCochain_complexScalar A U 1 c z)

end

/-! The actual comparison to native holomorphic H1 commutes with its
canonical complex scalar maps, as checked on all algebraic cocycles. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

variable (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) {I : Type} (U : I → A.carrier.Opens)

theorem cechAnalytificationH1_scalar (hU : iSup U = ⊤) (c : ℂ) :
    HomologicalComplex.homologyMap (CechClassScalars.algebraicCechScalarMap A U c) 1 ≫ Analytification.cechAnalytificationH1 A.variety U hU =
      Analytification.cechAnalytificationH1 A.variety U hU ≫
        (CategoryTheory.Sheaf.functorH (Opens.grothendieckTopology (TopCat.of A.variety.analyticSpace)) 1).map
          (RepresentationTheory.Theta.Geometric.Holomorphic.PicardPeriodQuotient.holomorphicScalarSheafMap A.variety.analyticModel A.variety.analyticSpace c) := by
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro x
  obtain ⟨z, hz, rfl⟩ := CechClasses.algebraicCechOneClass_surjective A.variety U x
  change Analytification.cechAnalytificationH1 A.variety U hU
    (HomologicalComplex.homologyMap (CechClassScalars.algebraicCechScalarMap A U c) 1 (CechClasses.algebraicCechOneClass A.variety U z hz)) =
      RepresentationTheory.Theta.Geometric.Holomorphic.PicardPeriodQuotient.holomorphicScalarH1 A.variety.analyticModel A.variety.analyticSpace c
        (Analytification.cechAnalytificationH1 A.variety U hU (CechClasses.algebraicCechOneClass A.variety U z hz))
  rw [CechClassScalars.algebraicCechOneClass_scalar, Analytification.cechAnalytificationH1_class, Analytification.cechAnalytificationH1_class]
  exact nativeCechOneClass_scalar A U hU c z hz

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Cech.AnalytificationScalars
