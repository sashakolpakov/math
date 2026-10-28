import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Proper.IntegralCohomologyInduction
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coherent.SupportInduction
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coherent.NilpotentInduction
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coherent.ClosedImageSupport
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.IntegralClosedSupport
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.PushforwardCohomologyFiniteness
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CoefficientCohomology.IsomorphismProperty

/-! # Coherent Cohomology -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Proper.CoherentCohomology

noncomputable section

/-! Finiteness of genuine coherent cohomology for a proper scheme over a Noetherian affine base, proved by Chow modification, generic comparison, and induction through actual closed supports and nilpotent layers. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace
open _root_.AlgebraicGeometry.Scheme.Modules
universe u

theorem proper_coherent_cohomologyFinite
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) [IsProper f]
    (M : X.Modules) [M.IsQuasicoherent] [M.IsFiniteType] : CoefficientCohomology.FinitenessProperty.ZariskiCohomology.CoefficientCohomologyFinite (Coefficient.ModulePresheaf.schemeCoefficientMap f) M := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : X.IsSeparated := ⟨by rw [← terminal.comp_from f]; infer_instance⟩
  have : IsNoetherianRing Γ(Spec (.of R), ⊤) := isNoetherianRing_of_ringEquiv R
    (Scheme.ΓSpecIso (.of R)).symm.commRingCatIsoToRingEquiv
  apply Coherent.SupportInduction.coherent_support_induction (CoefficientCohomology.FinitenessProperty.ZariskiCohomology.CoefficientCohomologyFinite (Coefficient.ModulePresheaf.schemeCoefficientMap f))
    (fun N hN => CoefficientCohomology.FinitenessProperty.ZariskiCohomology.CoefficientCohomologyFinite.of_isZero (Coefficient.ModulePresheaf.schemeCoefficientMap f) N hN) _ M
  intro Z hZ ih N _ _ hN
  let I := Scheme.IdealSheafData.vanishingIdeal Z
  have hIZ : I.support = Z := SetLike.coe_injective
    (Scheme.IdealSheafData.coe_support_vanishingIdeal Z)
  apply Coherent.NilpotentInduction.coherent_property_of_closed_support (CoefficientCohomology.FinitenessProperty.ZariskiCohomology.CoefficientCohomologyFinite (Coefficient.ModulePresheaf.schemeCoefficientMap f)) I _ N
    (hIZ.symm ▸ hN)
  intro Q _ _
  have : IsIntegral I.subscheme := IntegralClosedSupport.vanishingIdeal_subscheme_integral Z hZ
  apply (Affine.PushforwardCohomologyFiniteness.coefficientCohomologyFinite_affinePushforward_iff I.subschemeι f Q).mpr
  apply IntegralCohomologyInduction.properIntegral_cohomologyFinite_of_proper_support (I.subschemeι ≫ f) _ Q
  intro T _ _ hT
  let P := (pushforward I.subschemeι).obj T
  have : P.IsQuasicoherent := Quasicoherent.Image.quasiCompact_separated_directImage_quasicoherent I.subschemeι T
  have : P.IsFiniteType := Finite.ImageType.finite_directImage_finiteType I.subschemeι T
  have hr : Coherent.ClosedImageSupport.closedImage I.subschemeι ⊤ = Z := by
    apply SetLike.coe_injective
    change I.subschemeι '' Set.univ = (Z : Set X)
    rw [Set.image_univ, Scheme.IdealSheafData.range_subschemeι]
    exact congrArg (fun W : Closeds X => (W : Set X)) hIZ
  have hP : (Coherent.Annihilator.coherentAnnihilator P).support < Z := by
    rw [← hr]
    exact lt_of_le_of_lt (Coherent.ClosedImageSupport.coherent_pushforward_support_le_closedImage I.subschemeι T)
      (Coherent.ClosedImageSupport.closedImage_lt_range_of_lt_top I.subschemeι (Coherent.Annihilator.coherentAnnihilator T).support hT)
  exact (Affine.PushforwardCohomologyFiniteness.coefficientCohomologyFinite_affinePushforward_iff I.subschemeι f T).mp (ih P hP)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Proper.CoherentCohomology
