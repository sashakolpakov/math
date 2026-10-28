import OAI.AlgebraicGeometry.Resolution.Blowups.ControlPrefix.HomogenizedTransport

/-! # Whole Prefix Residual Transport -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups

noncomputable section

/-! Residual transport follows an arbitrary whole prefix, including prefixes assembled from several coefficient levels. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem Smooth.ControlPrefix.Construction.SmoothControlPrefix.exists_lower_control_same_blowups
    {m : ℕ} {X Y : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
    {J : X.IdealSheafData} {K : Y.IdealSheafData} (P : Smooth.ControlPrefix.Construction.SmoothControlPrefix m X f J Y g K)
    (b : ℕ) (hb : 0 < b) (hbm : b ≤ m) :
    ∀ (β : Type) [Fintype β] (D : β → X.IdealSheafData), P.uniformBoundaryCompatible β D →
      ∀ a : β → ℕ, ∃ (a' : P.endpointLabels β → ℕ)
        (Q : Smooth.ControlPrefix.Construction.SmoothControlPrefix b X f (Global.MixedBoundary.Construction.boundaryMonomialSheaf D a * J) Y g
          (Global.MixedBoundary.Construction.boundaryMonomialSheaf (P.endpointBoundary D) a' * K)), Smooth.ControlPrefix.Construction.SmoothControlPrefix.SameBlowups m b P Q := by
  induction P with
  | stop =>
      intro β _ D hD a
      exact ⟨a, .stop, .stop⟩
  | @blowup X hX hNX f J I hI hm hp hs hbl Y g K tail ih =>
      intro β _ D hD a
      obtain ⟨A, F, hF⟩ := hD.1
      let D' := CanonicalBoundaryTransform.Construction.globalBlowupCanonicalBoundary I hI D
      let a₁ := ResidualBoundaryMonomialUpdate.Construction.residualBoundaryMonomialExponents F a m b
      have hM : Global.MixedBoundary.Construction.boundaryMonomialSheaf D a ≤ I ^ (b - m) := by
        rw [Nat.sub_eq_zero_of_le hbm, pow_zero, Scheme.IdealSheafData.one_eq_top]
        exact le_top
      have hpTotal : Global.MixedBoundary.Construction.boundaryMonomialSheaf D a * J ≤ I ^ b := by
        intro U
        exact Ideal.mul_le_right.trans ((hp U).trans (Ideal.pow_le_pow_right hbm))
      have htransform : GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I (Global.MixedBoundary.Construction.boundaryMonomialSheaf D a * J) hI b =
          Global.MixedBoundary.Construction.boundaryMonomialSheaf D' a₁ * GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I J hI m :=
        A.residual_product_uniform_incidence F (fun i _ => hF i) J hI a m b hM hp
      obtain ⟨a', Q, hQ⟩ := ih (Option β) D' hD.2 a₁
      have hnext : ∃ R : Smooth.ControlPrefix.Construction.SmoothControlPrefix b (GlobalBlowup.Data.Construction.globalBlowup I hI) (GlobalBlowup.Data.Construction.globalBlowupToBase I hI ≫ f)
          (GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I (Global.MixedBoundary.Construction.boundaryMonomialSheaf D a * J) hI b) Y g
          (Global.MixedBoundary.Construction.boundaryMonomialSheaf (tail.endpointBoundary D') a' * K), Smooth.ControlPrefix.Construction.SmoothControlPrefix.SameBlowups m b tail R := by
        rw [htransform]
        exact ⟨Q, hQ⟩
      obtain ⟨R, hR⟩ := hnext
      exact ⟨a', .blowup I hI hb hpTotal hs hbl R, .blowup I hI hm hb hp hpTotal hs hbl hR⟩

end

end OAI.AlgebraicGeometry.Resolution.Blowups
