import OAI.AlgebraicGeometry.Resolution.Blowups.Locally.PrincipalIdealSheaf
import OAI.AlgebraicGeometry.Resolution.Blowups.GlobalControlled.Factorization
import OAI.AlgebraicGeometry.Resolution.Blowups.Affine.OpenBoundaryTransport
import OAI.AlgebraicGeometry.Resolution.Blowups.Global.GlobalUnitSequenceGeometry

/-! # Exceptional Principality -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Global

noncomputable section

/-! Every exceptional center pullback is locally principal, giving actual global principalization at unit endpoints. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem ExceptionalPrincipality.Construction.globalBlowup_center_locallyPrincipal
    {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X] (I : X.IdealSheafData) (hI : I ≠ ⊥) :
    Locally.PrincipalIdealSheaf.Construction.LocallyPrincipalIdealSheaf (I.comap (GlobalBlowup.Data.Construction.globalBlowupToBase I hI)) := by
  intro x
  obtain ⟨p, q, hq⟩ := GlobalControlled.Chart.Construction.exists_globalBlowupReesChart I hI x
  let R := Blowup.Charts.Construction.blowupChart (I.ideal p.1) p.2
  let j := GlobalControlled.Chart.Construction.globalBlowupReesChart I hI p.1 p.2
  let K := I.comap (GlobalBlowup.Data.Construction.globalBlowupToBase I hI)
  let a : R := Blowup.Charts.Construction.blowupChartConstants (I.ideal p.1) p.2 p.2.val
  have hK : K.comap j = Affine.QuotientKernel.Construction.affineQuotientKernel (Ideal.span {a}) :=
    (GlobalControlled.Factorization.Construction.totalIdeal_comap_globalBlowupReesChart I I hI p.1 p.2).trans
      (congrArg Affine.QuotientKernel.Construction.affineQuotientKernel (ExceptionalIdeal.Construction.blowupChart_extendedIdeal (I := I.ideal p.1) p.2))
  refine ⟨Affine.OpenBoundaryTransport.Construction.specOpenImage (.of R) j, ?_, (Affine.OpenBoundaryTransport.Construction.specOpenSectionEquiv (.of R) j).symm a, ?_⟩
  · rw [Affine.OpenBoundaryTransport.Construction.specOpenImage_eq_opensRange]
    exact ⟨q, hq⟩
  · exact Affine.OpenBoundaryTransport.Construction.specOpenSectionEquiv_equation (.of R) j K a hK

theorem UnitSequence.Construction.SmoothGlobalUnitSequence.exceptionalProduct_locallyPrincipal
    {X : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {J : X.IdealSheafData}
    (T : UnitSequence.Construction.SmoothGlobalUnitSequence X f J) : Locally.PrincipalIdealSheaf.Construction.LocallyPrincipalIdealSheaf T.exceptionalProduct := by
  induction T with
  | @terminal Y g hs => exact Locally.PrincipalIdealSheaf.Construction.LocallyPrincipalIdealSheaf.top Y
  | blowup I hI b hb hp hs hbl tail ih =>
      change Locally.PrincipalIdealSheaf.Construction.LocallyPrincipalIdealSheaf
        ((I.comap (tail.toBase ≫ GlobalBlowup.Data.Construction.globalBlowupToBase I hI)) ^ b * tail.exceptionalProduct)
      rw [Scheme.IdealSheafData.comap_comp]
      exact (((ExceptionalPrincipality.Construction.globalBlowup_center_locallyPrincipal I hI).comap tail.toBase).pow b).mul ih

theorem UnitSequence.Construction.SmoothGlobalUnitSequence.totalTransform_locallyPrincipal
    {X : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {J : X.IdealSheafData}
    (T : UnitSequence.Construction.SmoothGlobalUnitSequence X f J) : Locally.PrincipalIdealSheaf.Construction.LocallyPrincipalIdealSheaf (J.comap T.toBase) := by
  rw [← T.exceptionalProduct_eq_totalTransform]
  exact T.exceptionalProduct_locallyPrincipal

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Global
