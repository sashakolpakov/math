import OAI.AlgebraicGeometry.PELModuli.IntegralModel.GeometricAmpleNeighborhood
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Affine.BaseAmpleness

/-! # Noetherian Model Recovery -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.NoetherianModelRecovery

noncomputable section

/-! Ampleness on the original family follows from ample fibers and an
actual proper flat Noetherian model of its line bundle. The coefficient
map is arbitrary affine; no flatness or reducedness is required of it. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

theorem isAmple_of_noetherian_model
    {S T X Y : Scheme.{0}} [IsAffine S] [IsAffine T] [IsNoetherianRing Γ(T, ⊤)]
    (f : X ⟶ S) [IsProper f] (p : Y ⟶ T) [IsProper p] [Flat p]
    (q : X ⟶ Y) (b : S ⟶ T) [IsAffineHom b] (H : IsPullback q f p b)
    (L : Line.Bundles.LineBundle X) (K : Line.Bundles.LineBundle Y)
    (e : (K.pullback q).sheaf ≅ L.sheaf)
    (hL : ∀ x : S, (L.pullback (f.fiberι x)).IsAmple) : L.IsAmple := by
  have : X.IsSeparated := ⟨by rw [← terminal.comp_from f]; infer_instance⟩
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have hq : IsAffineHom q :=
    MorphismProperty.of_isPullback H.flip (inferInstance : IsAffineHom b)
  apply PELModuli.IntegralModel.Affine.BaseAmpleness.isAmple_of_affine_base_neighborhoods f L
  intro x
  let a := f.fiberι x
  let r := f.fiberToSpecResidueField x
  let g := S.fromSpecResidueField x ≫ b
  have hF : IsPullback (a ≫ q) r p g :=
    (IsPullback.of_hasPullback f (S.fromSpecResidueField x)).paste_horiz H
  let eF : (K.pullback (a ≫ q)).sheaf ≅ (L.pullback a).sheaf :=
    (Scheme.Modules.pullbackComp a q).symm.app K.sheaf ≪≫
      (Scheme.Modules.pullback a).mapIso e
  obtain ⟨U, hxU, _, hKU⟩ :=
    PELModuli.IntegralModel.GeometricAmpleNeighborhood.properFlat_exists_affine_ample_neighborhood_of_geometric_fiber
      p K (a ≫ q) r g hF ((hL x).of_iso eF.symm)
  let V := b ⁻¹ᵁ U
  let W := p ⁻¹ᵁ U
  have hx : x ∈ V := by
    change b x ∈ U
    have hg : g (IsLocalRing.closedPoint (S.residueField x)) = b x :=
      (Scheme.Hom.comp_apply (S.fromSpecResidueField x) b _).trans
        (congrArg b (S.fromSpecResidueField_apply x _))
    exact hg ▸ hxU
  have hpre : q ⁻¹ᵁ W = f ⁻¹ᵁ V := by
    change q ⁻¹ᵁ (p ⁻¹ᵁ U) = f ⁻¹ᵁ (b ⁻¹ᵁ U)
    rw [← Scheme.Hom.comp_preimage, H.w, Scheme.Hom.comp_preimage]
  refine ⟨V, hx, ?_⟩
  rw [← hpre]
  have : IsAffineHom (q ∣_ W) :=
    MorphismProperty.of_isPullback (isPullback_morphismRestrict q W).flip hq
  have h := hKU.pullback_of_isAffineHom (q ∣_ W)
  apply h.of_iso
  exact (Scheme.Modules.pullbackComp (q ∣_ W) W.ι).app K.sheaf ≪≫
    (Scheme.Modules.pullbackCongr (morphismRestrict_ι q W)).app K.sheaf ≪≫
    (Scheme.Modules.pullbackComp (q ⁻¹ᵁ W).ι q).symm.app K.sheaf ≪≫
    (Scheme.Modules.pullback (q ⁻¹ᵁ W).ι).mapIso e

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.NoetherianModelRecovery
