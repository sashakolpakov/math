import OAI.AlgebraicGeometry.Resolution.Blowups.Disjoint.FactorControlledTransform
import OAI.AlgebraicGeometry.Resolution.Blowups.Global.IntegralOrderSequenceExtension
import OAI.AlgebraicGeometry.Resolution.Blowups.Blowup.DisjointCenter

/-! # Factor Sequence Transport -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups

noncomputable section

/-! Integral-center continuations transport through the actual disjoint-factor blowup isomorphism. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem Global.MonomialSequence.Construction.SmoothFixedControlSequence.transport_integral_iso
    {b : ℕ} {V : Scheme} {g : V ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {L : V.IdealSheafData}
    (T : Global.MonomialSequence.Construction.SmoothFixedControlSequence b V g L) (hT : T.integralCenters)
    {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X]
    (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [Smooth f] (J : X.IdealSheafData) (hJ : J ≠ ⊥)
    (e : V ≅ X) (hg : e.hom ≫ f = g) (hL : J.comap e.hom = L) :
    ∃ U : Global.MonomialSequence.Construction.SmoothFixedControlSequence b X f J, U.integralCenters := by
  apply T.extend_integral_from_order_neighborhood X f J hJ e.hom hg hL _ hT
  intro x _
  refine ⟨e.inv x, ?_⟩
  change (e.inv ≫ e.hom) x = x
  rw [e.inv_hom_id]
  rfl

theorem Disjoint.FactorSequenceTransport.Construction.disjointFactor_integral_sequence_transport
    {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X]
    (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [Smooth f] (K L J : X.IdealSheafData)
    (hK : K ≠ ⊥) (hL : L ≠ ⊥) (hJ : J ≠ ⊥) (hdisjoint : K ⊔ L = ⊤)
    [Smooth (K.subschemeι ≫ f)] [Smooth (L.subschemeι ≫ f)]
    (b : ℕ) (hp : J ≤ (K * L) ^ b)
    (R : Global.MonomialSequence.Construction.SmoothFixedControlSequence b (GlobalBlowup.Data.Construction.globalBlowup (K * L) (Integral.IdealSheafProducts.Construction.idealSheaf_mul_ne_bot K L hK hL))
      (GlobalBlowup.Data.Construction.globalBlowupToBase (K * L) (Integral.IdealSheafProducts.Construction.idealSheaf_mul_ne_bot K L hK hL) ≫ f)
      (GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal (K * L) J (Integral.IdealSheafProducts.Construction.idealSheaf_mul_ne_bot K L hK hL) b))
    (hR : R.integralCenters) :
    ∃ S : Global.MonomialSequence.Construction.SmoothFixedControlSequence b (Disjoint.FactorBlowupIso.Construction.disjointFactorBlowup K L hK hL)
      (GlobalBlowup.Data.Construction.globalBlowupToBase (L.comap (GlobalBlowup.Data.Construction.globalBlowupToBase K hK))
        (GlobalBlowup.Nonzero.Construction.globalBlowup_totalIdeal_ne_bot K L hK hL) ≫ (GlobalBlowup.Data.Construction.globalBlowupToBase K hK ≫ f))
      (GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal (L.comap (GlobalBlowup.Data.Construction.globalBlowupToBase K hK))
        (GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal K J hK b) (GlobalBlowup.Nonzero.Construction.globalBlowup_totalIdeal_ne_bot K L hK hL) b),
      S.integralCenters := by
  let I := K * L
  have hI : I ≠ ⊥ := Integral.IdealSheafProducts.Construction.idealSheaf_mul_ne_bot K L hK hL
  let π := GlobalBlowup.Data.Construction.globalBlowupToBase I hI
  let κ := GlobalBlowup.Data.Construction.globalBlowupToBase K hK
  let L' := L.comap κ
  have hL' : L' ≠ ⊥ := GlobalBlowup.Nonzero.Construction.globalBlowup_totalIdeal_ne_bot K L hK hL
  let σ := GlobalBlowup.Data.Construction.globalBlowupToBase L' hL'
  let : Smooth (κ ≫ f) := Global.SmoothCenterBlowup.Construction.globalBlowup_smooth_of_smooth_center f K hK
  let : Smooth (L'.subschemeι ≫ (κ ≫ f)) := Blowup.DisjointCenter.Construction.globalBlowup_disjoint_center_smooth f K L hK hdisjoint
  let : Smooth (σ ≫ (κ ≫ f)) := Global.SmoothCenterBlowup.Construction.globalBlowup_smooth_of_smooth_center (κ ≫ f) L' hL'
  let e := Disjoint.FactorControlledTransform.Construction.disjointFactorBlowupIso K L hK hL hdisjoint
  have he : e.hom ≫ π = σ ≫ κ := Disjoint.FactorControlledTransform.Construction.disjointFactorBlowupIso_over K L hK hL hdisjoint
  have hei : e.inv ≫ (σ ≫ κ) = π := by
    rw [← he, ← Category.assoc, e.inv_hom_id, Category.id_comp]
  let J₂ := GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal L' (GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal K J hK b) hL' b
  have hJ₂ : J₂ ≠ ⊥ := GlobalBlowup.Nonzero.Construction.globalBlowupControlledIdeal_ne_bot L' _ hL' b
    (GlobalBlowup.Nonzero.Construction.globalBlowupControlledIdeal_ne_bot K J hK b hJ)
  apply R.transport_integral_iso hR (σ ≫ (κ ≫ f)) J₂ hJ₂ e.symm
  · change e.inv ≫ (σ ≫ (κ ≫ f)) = π ≫ f
    rw [← Category.assoc σ κ f, ← Category.assoc, hei]
  · have h := congrArg (fun N => N.comap e.inv) (Disjoint.FactorControlledTransform.Construction.disjointFactorBlowupIso_controlled K L J hK hL hdisjoint b hp)
    rw [← Scheme.IdealSheafData.comap_comp, e.inv_hom_id, Scheme.IdealSheafData.comap_id] at h
    exact h.symm

end

end OAI.AlgebraicGeometry.Resolution.Blowups
