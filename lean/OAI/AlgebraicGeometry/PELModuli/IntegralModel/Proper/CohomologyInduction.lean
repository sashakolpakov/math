import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Proper.AcyclicLine
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.GenericLineFrame
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.GenericModuleTrivialization
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.CohomologyFiniteCoproducts
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.CoherentSupportSplit

/-! # Cohomology Induction -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Proper.CohomologyInduction

noncomputable section

/-! The integral step of proper cohomology finiteness: compare an
arbitrary coherent sheaf with a finite sum of the actual good sheaf
constructed by Chow modification, on a constructed nonempty affine open. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace
open _root_.AlgebraicGeometry.Scheme.Modules

theorem properIntegral_cohomologyFinite_of_proper_support
    {R : Type} [CommRing R] [IsNoetherianRing R]
    {X : Scheme.{0}} [IsIntegral X] (f : X ⟶ Spec (.of R)) [IsProper f]
    (hsmall : ∀ (Q : X.Modules) [Q.IsQuasicoherent] [Q.IsFiniteType],
      (CoherentAnnihilator.coherentAnnihilator Q).support < ⊤ → CohomologyExactFiniteness.BaseCohomologyFinite f Q)
    (M : X.Modules) [M.IsQuasicoherent] [M.IsFiniteType] : CohomologyExactFiniteness.BaseCohomologyFinite f M := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : IsNoetherianRing Γ(Spec (.of R), ⊤) := isNoetherianRing_of_ringEquiv R
    (Scheme.ΓSpecIso (.of R)).symm.commRingCatIsoToRingEquiv
  obtain ⟨G, hGq, hGt, hG, _, U, hU, _, L, ⟨eG⟩⟩ :=
    AcyclicLine.properIntegral_exists_coherent_generic_line_finite_cohomology f
  let := hGq
  let := hGt
  let := hU
  obtain ⟨V, _, hV, hVa, ⟨bG⟩⟩ := GenericLineFrame.exists_generic_line_frame G U L eG
  let := hV
  obtain ⟨W, hWV, hW, _, n, ⟨bM⟩⟩ := GenericModuleTrivialization.exists_generic_module_trivialization M ⟨V, hVa⟩
  let C := ∐ fun _ : Fin n => G
  have : C.IsQuasicoherent := SheafCohomology.Projective.Quasicoherent.Scheme.Modules.isQuasicoherent_coproduct _ (fun _ => hGq)
  have : C.IsFiniteType := SheafCohomology.Projective.Quasicoherent.Scheme.Modules.isFiniteType_fin_coproduct _ (fun _ => hGq) (fun _ => hGt)
  let eC : C.restrict W.ι ≅ ∐ fun _ : Fin n => SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj W.toScheme :=
    PreservesCoproduct.iso (restrictFunctor W.ι) (fun _ : Fin n => G) ≪≫
      Sigma.mapIso (fun _ => SheafCohomology.Projective.OpenRestrictionComposition.nativeOpenFrame hWV bG)
  apply (CohomologyComparison.baseCohomologyFinite_iff_of_open_iso f W _ M C (bM.symm ≪≫ eC.symm)).mpr
  · exact CohomologyExactFiniteness.BaseCohomologyFinite.coproduct f (fun _ : Fin n => G) (fun _ => hG)
  · intro Q hQq hQt hQ
    let := hQq
    let := hQt
    apply hsmall Q
    apply lt_top_iff_ne_top.mpr
    intro heq
    obtain ⟨x⟩ := hW
    have hx : x.val ∈ (CoherentAnnihilator.coherentAnnihilator Q).support := by rw [heq]; trivial
    exact (CoherentAnnihilator.coherentAnnihilator_mem_support_iff Q x.val).mp hx
      ((ModuleVanishingOpen.module_restrict_isZero_iff_le_vanishingOpen Q W).mp hQ x.property)

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Proper.CohomologyInduction
