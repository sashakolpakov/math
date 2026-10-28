import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.Quasicoherence
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Field.ExtensionSectionDimension
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Intrinsic.SectionPolynomial
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Proper.CoherentCohomology
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CoefficientCohomology.DegreeZero

/-! # Field Section Polynomial -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Genuine section Hilbert polynomials are preserved and reflected by
an arbitrary Cartesian field extension with an actual line-bundle
comparison. Properness supplies finite-dimensionality on both sides. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u

theorem Cartesian.FieldSectionPolynomial.properField_lineBundle_sectionModule_finite
    {K : Type u} [Field K] {X : Scheme.{u}} (p : X ⟶ Spec (.of K)) [IsProper p]
    (L : Line.Bundles.LineBundle X) : Module.Finite K ((Coefficient.GlobalSectionsFunctor.schemeGlobalSectionsFunctor p).obj L.sheaf) := by
  have : L.sheaf.IsQuasicoherent := L.isQuasicoherent
  have : L.sheaf.IsFiniteType := L.isFiniteType
  have : Module.Finite K ((Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor
      (Coefficient.ModulePresheaf.schemeCoefficientMap p) 0).obj L.sheaf) := Proper.CoherentCohomology.proper_coherent_cohomologyFinite p L.sheaf 0
  let e := CoefficientCohomology.DegreeZero.ZariskiCohomology.coefficientCohomologyZeroSectionsEquiv (Coefficient.ModulePresheaf.schemeCoefficientMap p) L.sheaf
  exact Module.Finite.of_surjective e.toLinearMap e.surjective

variable {K F : Type u} [Field K] [Field F] {X Y : Scheme.{u}}
variable {p : X ⟶ Spec (.of K)} {q : Y ⟶ Spec (.of F)} [IsProper p]
variable (φ : CommRingCat.of K ⟶ CommRingCat.of F) {a : Y ⟶ X}
variable (H : IsPullback a q p (Spec.map φ)) (L : Line.Bundles.LineBundle X) (M : Line.Bundles.LineBundle Y)
variable (e : (L.pullback a).sheaf ≅ M.sheaf)

include φ H e in
theorem Cartesian.FieldSectionPolynomial.cartesianFieldExtension_powerSection_finrank (m : ℕ) :
    Module.finrank F ((Coefficient.GlobalSectionsFunctor.schemeGlobalSectionsFunctor q).obj (M.tensorPower m).sheaf) =
      Module.finrank K ((Coefficient.GlobalSectionsFunctor.schemeGlobalSectionsFunctor p).obj (L.tensorPower m).sheaf) := by
  let c := pullback.fst p (Spec.map φ)
  let b := pullback.snd p (Spec.map φ)
  let E : Over.mk q ≅ (Over.pullback (Spec.map φ)).obj (Over.mk p) :=
    Over.isoMk H.isoPullback H.isoPullback_hom_snd
  let ep : ((L.pullback c).pullback E.hom.left).sheaf ≅ M.sheaf :=
    (Scheme.Modules.pullbackComp E.hom.left c).app L.sheaf ≪≫
      (Scheme.Modules.pullbackCongr H.isoPullback_hom_fst).app L.sheaf ≪≫ e
  let es := (Coefficient.GlobalSectionsFunctor.schemeGlobalSectionsIso b (L.powerBaseChangeIso c m)).trans
    (Intrinsic.LineBundleSections.lineBundlePowerSectionsOverIso E (L.pullback c) M ep m)
  exact es.finrank_eq.symm.trans (HilbertConstruction.Field.ExtensionSectionDimension.fieldExtension_lineBundle_sections_finrank p φ (L.tensorPower m))

include φ H e in
theorem Line.Bundles.LineBundle.hasSectionHilbertPolynomial_iff_of_cartesianFieldExtension (P : Polynomial ℚ) :
    L.HasSectionHilbertPolynomial p P ↔ M.HasSectionHilbertPolynomial q P := by
  have : IsProper q := MorphismProperty.of_isPullback (P := @IsProper) H inferInstance
  constructor
  · rintro ⟨b, hb⟩
    refine ⟨b, fun m hm => ⟨Cartesian.FieldSectionPolynomial.properField_lineBundle_sectionModule_finite q (M.tensorPower m), ?_⟩⟩
    exact (hb m hm).2.trans (congrArg (fun n : ℕ => (n : ℚ))
      (Cartesian.FieldSectionPolynomial.cartesianFieldExtension_powerSection_finrank φ H L M e m).symm)
  · rintro ⟨b, hb⟩
    refine ⟨b, fun m hm => ⟨Cartesian.FieldSectionPolynomial.properField_lineBundle_sectionModule_finite p (L.tensorPower m), ?_⟩⟩
    exact (hb m hm).2.trans (congrArg (fun n : ℕ => (n : ℚ))
      (Cartesian.FieldSectionPolynomial.cartesianFieldExtension_powerSection_finrank φ H L M e m))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
