import OAI.AlgebraicGeometry.PELModuli.IntegralModel.BasicOpenSectionNonvanishing
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Open.ImageAmpleness
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.AffinePullback

/-! # Base Ampleness -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Affine.BaseAmpleness

noncomputable section

/-! Ampleness near every base point is global ampleness over an affine
base. The proof extends actual sections on principal opens. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem isAmple_of_basicOpen_neighborhoods
    {X : Scheme.{u}} [X.IsSeparated] [CompactSpace X] (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X)
    (h : ∀ x : X, ∃ r : Γ(X, ⊤), x ∈ X.basicOpen r ∧
      (L.pullback (X.basicOpen r).ι).IsAmple) : L.IsAmple := by
  apply L.isAmple_iff_tensorPower.mpr
  refine ⟨isCompact_univ, fun x => ?_⟩
  obtain ⟨r, hxr, hL⟩ := h x
  let U := X.basicOpen r
  obtain ⟨n, hn, t, ht, ha⟩ := ((L.pullback U.ι).isAmple_iff_tensorPower.mp hL).2 ⟨x, hxr⟩
  let e : ((L.pullback U.ι).tensorPower n).sheaf ≅
      (BasicOpenSectionLifts.restrictedLineBundle (L.tensorPower n) U).sheaf :=
    (L.powerBaseChangeIso U.ι n).symm ≪≫
      ((Scheme.Modules.restrictFunctorIsoPullback U.ι).app (L.tensorPower n).sheaf).symm
  obtain ⟨q, hq⟩ := BasicOpenSectionNonvanishing.exists_global_section_nonvanishing_eq_basicOpen_image (L.tensorPower n) r (t ≫ e.hom)
  rw [AbelianModuli.HilbertConstruction.Ample.Powers.sectionNonvanishing_comp_iso] at hq
  refine ⟨n, hn, q, ?_, ?_⟩
  · rw [hq]
    exact ⟨⟨x, hxr⟩, ht, rfl⟩
  · rw [hq]
    exact ha.image_of_isOpenImmersion U.ι

theorem isAmple_of_affine_base_neighborhoods
    {X S : Scheme.{u}} [X.IsSeparated] [CompactSpace X] [IsAffine S]
    (f : X ⟶ S) (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X)
    (h : ∀ x : S, ∃ U : S.Opens, x ∈ U ∧ (L.pullback (f ⁻¹ᵁ U).ι).IsAmple) :
    L.IsAmple := by
  apply isAmple_of_basicOpen_neighborhoods L
  intro x
  obtain ⟨U, hxU, hL⟩ := h (f x)
  obtain ⟨r, hr, hxr⟩ := (isAffineOpen_top S).exists_basicOpen_le ⟨f x, hxU⟩ (by trivial)
  let a := f.appTop r
  let V := f ⁻¹ᵁ U
  have ha : x ∈ X.basicOpen a := by
    rw [← f.preimage_basicOpen_top]
    exact hxr
  have hsub : X.basicOpen a ≤ V := by
    rw [← f.preimage_basicOpen_top]
    exact f.preimage_mono hr
  let W := V.toScheme.basicOpen (V.ι.appTop a)
  have hW : ((L.pullback V.ι).pullback W.ι).IsAmple := hL.pullback_of_isAffineHom W.ι
  have he : V.ι ''ᵁ W = X.basicOpen a := by
    rw [show W = V.ι ⁻¹ᵁ X.basicOpen a from (V.ι.preimage_basicOpen_top a).symm,
      Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι,
      inf_eq_right.mpr hsub]
  have ham := Open.ImageAmpleness.isAmple_on_open_image V.ι L W hW
  rw [he] at ham
  exact ⟨a, ha, ham⟩

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Affine.BaseAmpleness
