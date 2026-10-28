import OAI.AlgebraicGeometry.Divisors.LineBundles.Affine.SchemeSection
import OAI.AlgebraicGeometry.Divisors.LineBundles.Section.OpenRestriction
import Mathlib.AlgebraicGeometry.IdealSheaf.Basic

/-! # Section Chart Cone -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Affine.SectionChartCone.BundleCycles

noncomputable section

/-! # LineBundleCycles: the canonical normal-cone isomorphism on actual affine section charts -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

theorem affineSectionChart_normalCone_bijective {X Y : Scheme.{0}} (p : Y ⟶ X) [Smooth p]
    (s : X ⟶ Y) [IsClosedImmersion s] (hs : s ≫ p = 𝟙 X)
    (U : Y.Opens) (V : X.Opens) (hUaff : IsAffineOpen U) (hVaff : IsAffineOpen V)
    (hV : V ≤ s ⁻¹ᵁ U) (hU : U ≤ p ⁻¹ᵁ V) :
    Function.Bijective (Normal.ConeSymmetric.BundleCycles.normalConeSymmetricMap (s.ker.ideal ⟨U, hUaff⟩)) := by
  have : IsAffine U.toScheme := hUaff
  have : IsAffine V.toScheme := hVaff
  let q := Section.OpenRestriction.BundleCycles.sectionOpenProjection p U V hU
  let t := Section.OpenRestriction.BundleCycles.sectionOpenMap s U V hV
  have ht : t ≫ q = 𝟙 V.toScheme := Section.OpenRestriction.BundleCycles.sectionOpen_retraction p s hs U V hV hU
  have h := SchemeSection.BundleCycles.AffineSchemeSection.normalConeSymmetricMap_bijective q t ht
  have he : s ⁻¹ᵁ U = V := Section.OpenRestriction.BundleCycles.sectionOpen_preimage p s hs U V hV hU
  have : IsIso (X.homOfLE hV) := by
    change IsIso (X.isoOfEq he.symm).hom
    infer_instance
  let W : U.toScheme.affineOpens := ⟨⊤, isAffineOpen_top U.toScheme⟩
  let W' : Y.affineOpens := ⟨U.ι ''ᵁ W.1, W.2.image_of_isOpenImmersion U.ι⟩
  have hker : RingHom.ker t.appTop.hom = s.ker.ideal W' := by
    have h₁ : RingHom.ker t.appTop.hom = t.ker.ideal W := (Scheme.Hom.ker_apply t W).symm
    have h₂ : t.ker.ideal W = (morphismRestrict s U).ker.ideal W :=
      congrArg (fun K : U.toScheme.IdealSheafData => K.ideal W)
        (Scheme.Hom.ker_comp_of_isIso (X.homOfLE hV) (morphismRestrict s U))
    have h₃ : (morphismRestrict s U).ker.ideal W = s.ker.ideal W' := Scheme.ker_morphismRestrict_ideal s U W
    exact h₁.trans (h₂.trans h₃)
  have hW : Function.Bijective (Normal.ConeSymmetric.BundleCycles.normalConeSymmetricMap (s.ker.ideal W')) := hker ▸ h
  have hW' : W' = ⟨U, hUaff⟩ := Subtype.ext U.ι_image_top
  exact (congrArg (fun Z : Y.affineOpens => Function.Bijective (Normal.ConeSymmetric.BundleCycles.normalConeSymmetricMap (s.ker.ideal Z))) hW') ▸ hW

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Affine.SectionChartCone.BundleCycles
