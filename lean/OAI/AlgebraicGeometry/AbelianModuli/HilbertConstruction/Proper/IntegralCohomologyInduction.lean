import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Proper.IntegralGoodCohomologySheaf
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.GenericLineFrame
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.GenericModuleTrivialization
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.NestedOpenModuleFrames
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CoefficientCohomology.FiniteCoproducts
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Quasicoherent.FiniteCoproducts
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CohomologyOpenComparison
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coherent.SupportSplitting

/-! # Integral Cohomology Induction -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Proper.IntegralCohomologyInduction

noncomputable section

/-! Proper integral coherent cohomology reduces to smaller supports by comparison with a constructed finite sum of a generic line sheaf. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace
open _root_.AlgebraicGeometry.Scheme.Modules
universe u

theorem properIntegral_cohomologyFinite_of_proper_support
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    {X : Scheme.{u}} [IsIntegral X] (f : X ⟶ Spec (.of R)) [IsProper f]
    (hsmall : ∀ (Q : X.Modules) [Q.IsQuasicoherent] [Q.IsFiniteType],
      (Coherent.Annihilator.coherentAnnihilator Q).support < ⊤ → CoefficientCohomology.FinitenessProperty.ZariskiCohomology.CoefficientCohomologyFinite (Coefficient.ModulePresheaf.schemeCoefficientMap f) Q)
    (M : X.Modules) [M.IsQuasicoherent] [M.IsFiniteType] : CoefficientCohomology.FinitenessProperty.ZariskiCohomology.CoefficientCohomologyFinite (Coefficient.ModulePresheaf.schemeCoefficientMap f) M := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : IsNoetherianRing Γ(Spec (.of R), ⊤) := isNoetherianRing_of_ringEquiv R
    (Scheme.ΓSpecIso (.of R)).symm.commRingCatIsoToRingEquiv
  obtain ⟨G, hGq, hGt, hG, _, U, hU, _, L, ⟨eG⟩⟩ :=
    IntegralGoodCohomologySheaf.properIntegral_exists_coherent_generic_line_finite_cohomology f
  let := hGq
  let := hGt
  let := hU
  obtain ⟨V, _, hV, hVa, ⟨bG⟩⟩ := GenericLineFrame.exists_generic_line_frame G U L eG
  let := hV
  obtain ⟨W, hWV, hW, _, n, ⟨bM⟩⟩ := GenericModuleTrivialization.exists_generic_module_trivialization M ⟨V, hVa⟩
  let C := ∐ fun _ : ULift.{u} (Fin n) => G
  have : C.IsQuasicoherent := Quasicoherent.Coproducts.module_quasicoherent_coproduct _ (fun _ => hGq)
  have : C.IsFiniteType := Quasicoherent.FiniteCoproducts.module_finiteType_finite_coproduct _ (fun _ => hGq) (fun _ => hGt)
  let eC : C.restrict W.ι ≅ ∐ fun _ : ULift.{u} (Fin n) => Line.Bundles.structureModule W.toScheme :=
    PreservesCoproduct.iso (restrictFunctor W.ι) (fun _ : ULift.{u} (Fin n) => G) ≪≫
      Sigma.mapIso (fun _ => NestedOpenModuleFrames.nativeOpenFrame hWV bG)
  apply (CohomologyOpenComparison.coefficientCohomologyFinite_iff_of_open_iso (Coefficient.ModulePresheaf.schemeCoefficientMap f) W _ M C (bM.symm ≪≫ eC.symm)).mpr
  · exact CoefficientCohomology.FinitenessProperty.ZariskiCohomology.CoefficientCohomologyFinite.coproduct (Coefficient.ModulePresheaf.schemeCoefficientMap f) (fun _ : ULift.{u} (Fin n) => G) (fun _ => hG)
  · intro Q hQq hQt hQ
    let := hQq
    let := hQt
    apply hsmall Q
    apply lt_top_iff_ne_top.mpr
    intro heq
    obtain ⟨x⟩ := hW
    have hx : x.val ∈ (Coherent.Annihilator.coherentAnnihilator Q).support := by rw [heq]; trivial
    exact (Coherent.Annihilator.coherentAnnihilator_mem_support_iff Q x.val).mp hx
      ((Module.VanishingOpen.module_restrict_isZero_iff_le_vanishingOpen Q W).mp hQ x.property)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Proper.IntegralCohomologyInduction
