import OAI.AlgebraicGeometry.Resolution.Blowups.SymmetricCoordinateModelCenter
import OAI.AlgebraicGeometry.Resolution.Blowups.Global.PrincipalBlowup
import OAI.AlgebraicGeometry.Resolution.Blowups.SupportedBoundaryCenterExtension

/-! # Program Center Pattern -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups

noncomputable section

/-! Before a symmetric coordinate program blows up the whole coordinate subspace, all its actual centers are empty. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

def Smooth.ControlPrefix.Construction.SmoothControlPrefix.UnitUntilWhole {X Y : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
    {J : X.IdealSheafData} {K : Y.IdealSheafData} (P : Smooth.ControlPrefix.Construction.SmoothControlPrefix 1 X f J Y g K) : Prop := by
  induction P with
  | stop => exact True
  | @blowup X _ _ f J C hC hb hp hs hbl Y g K tail ih => exact C = J ∨ C = ⊤ ∧ ih

theorem Smooth.ControlPrefix.Construction.SmoothControlPrefix.EtaleSymmetric.unitUntilWhole_of_coordinate_model
    {X Y : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
    {J : X.IdealSheafData} {K : Y.IdealSheafData} (P : Smooth.ControlPrefix.Construction.SmoothControlPrefix 1 X f J Y g K) :
    P.EtaleSymmetric → ∀ {σ τ : Type} [Fintype σ] [Fintype τ]
      (q : Spec (.of (MvPolynomial (σ ⊕ τ) ℂ)) ⟶ X) [IsIso q],
      q ≫ f = ComplexAffineDifferentialIdeal.Construction.complexSpecStructure (MvPolynomial (σ ⊕ τ) ℂ) →
      J.comap q = Affine.QuotientKernel.Construction.affineQuotientKernel (RingHom.ker Coordinate.SubspaceIdeal.Construction.polynomialCoordinateProjection.toRingHom) →
      P.UnitUntilWhole := by
  induction P with
  | stop => intros; trivial
  | @blowup X hX hNX f J C hC hb hp hs hbl Y g K tail ih =>
      intro H σ τ _ _ q _ hf hJ
      change C = J ∨ C = ⊤ ∧ tail.UnitUntilWhole
      rcases H.first_center_of_coordinate_model C hC hp hs hbl tail q hf hJ with h | h
      · exact Or.inl h
      · subst C
        refine Or.inr ⟨rfl, ?_⟩
        let π := GlobalBlowup.Data.Construction.globalBlowupToBase ⊤ hC
        let : IsIso π := Global.PrincipalBlowup.Construction.globalBlowupToBase_isIso_of_locallyPrincipal ⊤ hC (Locally.PrincipalIdealSheaf.Construction.LocallyPrincipalIdealSheaf.top X)
        have htrans : GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal ⊤ J hC 1 = J.comap π :=
          Global.PrincipalBlowup.Construction.globalBlowupControlledIdeal_top_center J hC 1
        have HT := H.tail_of_isomorphic_step ⊤ hC hb hp hs hbl tail htrans
        apply ih HT (q ≫ inv π)
        · change (q ≫ inv π) ≫ (π ≫ f) = _
          simpa only [Category.assoc, IsIso.inv_hom_id_assoc] using hf
        · rw [htrans, ← Scheme.IdealSheafData.comap_comp, Category.assoc, IsIso.inv_hom_id,
            Category.comp_id, hJ]

end

end OAI.AlgebraicGeometry.Resolution.Blowups
