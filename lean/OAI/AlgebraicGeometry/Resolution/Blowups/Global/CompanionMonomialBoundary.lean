import OAI.AlgebraicGeometry.Resolution.Blowups.GlobalBoundary.CompanionCompatibility
import OAI.AlgebraicGeometry.Resolution.Blowups.Global.AdmissibleMonomialTransform

/-! # Companion Monomial Boundary -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Global

noncomputable section

/-! Companion phases preserve an actual global monomial exceptional factor in their evolving boundary. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem CompanionSequence.Construction.SmoothGlobalCompanionSequence.terminal_monomial_boundary
    {m b : ℕ} {X : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {M J : X.IdealSheafData}
    (T : CompanionSequence.Construction.SmoothGlobalCompanionSequence m b X f M J) :
    ∀ (β : Type) [Fintype β] (D : β → X.IdealSheafData) (a : β → ℕ),
      (∀ l, D l ≠ ⊥) → M = MixedBoundary.Construction.boundaryMonomialSheaf D a → T.integralCenters →
      T.boundaryCompatible β D →
      ∃ (γ : Type) (inst : Fintype γ), letI := inst
        ∃ (E : γ → T.endpoint.IdealSheafData) (c : γ → ℕ),
          (∀ l, E l ≠ ⊥) ∧ T.exceptionalIdeal = MixedBoundary.Construction.boundaryMonomialSheaf E c ∧
          Nonempty (MonomialBoundaryAtlas.Construction.GlobalMonomialBoundaryAtlas (T.toBase ≫ f) E [Finset.univ]) := by
  induction T with
  | @terminal Y g hs M J hb hd =>
      intro β inst D a hD hM _ hB
      refine ⟨β, inst, D, a, hD, hM, ?_⟩
      change Nonempty (MonomialBoundaryAtlas.Construction.GlobalMonomialBoundaryAtlas (𝟙 Y ≫ g) D [Finset.univ])
      rw [Category.id_comp]
      exact hB
  | @blowup Y hY hN g hg M J hb I hI hM hJ hs hbl tail ih =>
      intro β _ D a hD hfactor hcenters hB
      change IsIntegral I.subscheme ∧ tail.integralCenters at hcenters
      change Nonempty (CanonicalBoundaryAtlas.Construction.GlobalMixedCenterAtlas g I D) ∧
        tail.boundaryCompatible (Option β) (CanonicalBoundaryTransform.Construction.globalBlowupCanonicalBoundary I hI D) at hB
      let : IsIntegral I.subscheme := hcenters.1
      obtain ⟨A⟩ := hB.1
      let D' := CanonicalBoundaryTransform.Construction.globalBlowupCanonicalBoundary I hI D
      let a' := Boundary.MonomialSchedule.Construction.boundaryScheduleExponents a (b - m) (AdmissibleMonomialTransform.Construction.integralCenterBoundaryLabels I D)
      have he : GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I M hI (b - m) = MixedBoundary.Construction.boundaryMonomialSheaf D' a' := by
        rw [hfactor]
        exact A.monomial_transform_integral_center hI a (b - m) (hfactor ▸ hM)
      obtain ⟨γ, inst, E, c, hE, hfactor', hA⟩ := ih (Option β) D' a'
        (CanonicalBoundaryTransform.Construction.globalBlowupCanonicalBoundary_ne_bot I hI D hD) he hcenters.2 hB.2
      refine ⟨γ, inst, E, c, hE, hfactor', ?_⟩
      change Nonempty (MonomialBoundaryAtlas.Construction.GlobalMonomialBoundaryAtlas ((tail.toBase ≫ GlobalBlowup.Data.Construction.globalBlowupToBase I hI) ≫ g) E [Finset.univ])
      rw [Category.assoc]
      exact hA

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Global
