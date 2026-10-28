import OAI.AlgebraicGeometry.Resolution.Blowups.PrincipalControlledTransform
import OAI.AlgebraicGeometry.Resolution.Blowups.Global.ExceptionalPrincipality
import OAI.AlgebraicGeometry.Resolution.Blowups.GlobalBlowup.MapGluing

/-! # Principality -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.GlobalControlled.Principality.Construction

noncomputable section

/-! Local principality survives the actual controlled transform at every permissible global blowup. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X]

theorem exists_globalBlowupReesChart_over_affineOpen
    (I : X.IdealSheafData) (hI : I ≠ ⊥) (U : X.affineOpens)
    (x : GlobalBlowup.Data.Construction.globalBlowup I hI) (hx : GlobalBlowup.Data.Construction.globalBlowupToBase I hI x ∈ U.1) :
    ∃ a : I.ideal U, ∃ p : PrimeSpectrum (Blowup.Charts.Construction.blowupChart (I.ideal U) a), Chart.Construction.globalBlowupReesChart I hI U a p = x := by
  have hr : x ∈ (GlobalBlowup.Data.Construction.globalBlowupChart I hI U).opensRange := by
    rw [GlobalBlowup.MapGluing.Construction.globalBlowupChart_opensRange]
    exact hx
  obtain ⟨q, hq⟩ := hr
  obtain ⟨a, p, hp⟩ := (Blowup.Cover.Construction.affineBlowupAffineCover (I.ideal U)).openCover.exists_eq q
  change I.ideal U at a
  refine ⟨a, p, ?_⟩
  change GlobalBlowup.Data.Construction.globalBlowupChart I hI U
    (Proj.awayι (ReesGrading.Construction.reesGrade (I.ideal U)) (Blowup.Charts.Construction.reesGenerator (I.ideal U) a)
      (Blowup.Charts.Construction.reesGenerator_mem (I.ideal U) a) (by decide) p) = x
  exact (congrArg (GlobalBlowup.Data.Construction.globalBlowupChart I hI U) hp).trans hq

theorem globalBlowupControlledIdeal_locallyPrincipal
    (I J : X.IdealSheafData) (hI : I ≠ ⊥) (b : ℕ) (hp : J ≤ I ^ b)
    (hJ : Locally.PrincipalIdealSheaf.Construction.LocallyPrincipalIdealSheaf J) :
    Locally.PrincipalIdealSheaf.Construction.LocallyPrincipalIdealSheaf (GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I J hI b) := by
  intro x
  obtain ⟨U, hxU, z, hz⟩ := hJ (GlobalBlowup.Data.Construction.globalBlowupToBase I hI x)
  obtain ⟨a, p, hpoint⟩ := exists_globalBlowupReesChart_over_affineOpen I hI U x hxU
  have hperm : Ideal.span {z} ≤ (I.ideal U) ^ b := by
    rw [← hz]
    exact hp U
  obtain ⟨r, hr⟩ := PrincipalControlledTransform.Construction.exists_principal_controlled_transform_generator (I.ideal U) z b a hperm
  let R := Blowup.Charts.Construction.blowupChart (I.ideal U) a
  let j := Chart.Construction.globalBlowupReesChart I hI U a
  let K := GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I J hI b
  have hK : K.comap j = Affine.QuotientKernel.Construction.affineQuotientKernel (Ideal.span {r}) := by
    change (GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I J hI b).comap (Chart.Construction.globalBlowupReesChart I hI U a) = _
    rw [Chart.Construction.globalBlowupControlledIdeal_comap_reesChart, hz, hr]
  refine ⟨Affine.OpenBoundaryTransport.Construction.specOpenImage (.of R) j, ?_, (Affine.OpenBoundaryTransport.Construction.specOpenSectionEquiv (.of R) j).symm r, ?_⟩
  · rw [Affine.OpenBoundaryTransport.Construction.specOpenImage_eq_opensRange]
    exact ⟨p, hpoint⟩
  · exact Affine.OpenBoundaryTransport.Construction.specOpenSectionEquiv_equation (.of R) j K r hK

end

end OAI.AlgebraicGeometry.Resolution.Blowups.GlobalControlled.Principality.Construction
