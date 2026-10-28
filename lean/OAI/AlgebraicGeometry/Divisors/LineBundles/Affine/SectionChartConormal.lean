import OAI.AlgebraicGeometry.Divisors.LineBundles.Affine.SectionChartCone
import OAI.AlgebraicGeometry.Divisors.LineBundles.Section.QuotientProjective

/-! # Section Chart Conormal -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Affine.SectionChartConormal.BundleCycles

noncomputable section

/-! # LineBundleCycles: finite projective conormals on actual affine smooth-section charts -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

theorem AffineSchemeSection.conormal_finite_projective {X Y : Scheme.{0}}
    [IsAffine X] [IsAffine Y] (p : Y ⟶ X) [Smooth p]
    (s : X ⟶ Y) (hs : s ≫ p = 𝟙 X) :
    Module.Finite (Γ(Y, ⊤) ⧸ RingHom.ker s.appTop.hom) (RingHom.ker s.appTop.hom).Cotangent ∧
    Module.Projective (Γ(Y, ⊤) ⧸ RingHom.ker s.appTop.hom) (RingHom.ker s.appTop.hom).Cotangent := by
  let := SchemeSection.BundleCycles.AffineSchemeSection.baseAlgebra p
  let := SchemeSection.BundleCycles.AffineSchemeSection.quotientAlgebra s
  let := SchemeSection.BundleCycles.AffineSchemeSection.scalarTower p s hs
  let := SchemeSection.BundleCycles.AffineSchemeSection.sectionRing_smooth p
  exact ⟨Section.QuotientProjective.BundleCycles.sectionQuotientConormal_finite Γ(X, ⊤) Γ(Y, ⊤),
    Section.QuotientProjective.BundleCycles.sectionQuotientConormal_projective Γ(X, ⊤) Γ(Y, ⊤)⟩

theorem affineSectionChart_conormal_finite_projective {X Y : Scheme.{0}} (p : Y ⟶ X) [Smooth p]
    (s : X ⟶ Y) [IsClosedImmersion s] (hs : s ≫ p = 𝟙 X)
    (U : Y.Opens) (V : X.Opens) (hUaff : IsAffineOpen U) (hVaff : IsAffineOpen V)
    (hV : V ≤ s ⁻¹ᵁ U) (hU : U ≤ p ⁻¹ᵁ V) :
    Module.Finite (Γ(Y, U) ⧸ s.ker.ideal ⟨U, hUaff⟩) (s.ker.ideal ⟨U, hUaff⟩).Cotangent ∧
    Module.Projective (Γ(Y, U) ⧸ s.ker.ideal ⟨U, hUaff⟩) (s.ker.ideal ⟨U, hUaff⟩).Cotangent := by
  have : IsAffine U.toScheme := hUaff
  have : IsAffine V.toScheme := hVaff
  let q := Section.OpenRestriction.BundleCycles.sectionOpenProjection p U V hU
  let t := Section.OpenRestriction.BundleCycles.sectionOpenMap s U V hV
  have ht : t ≫ q = 𝟙 V.toScheme := Section.OpenRestriction.BundleCycles.sectionOpen_retraction p s hs U V hV hU
  have h := AffineSchemeSection.conormal_finite_projective q t ht
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
  have hW : Module.Finite (Γ(Y, W'.1) ⧸ s.ker.ideal W') (s.ker.ideal W').Cotangent ∧
      Module.Projective (Γ(Y, W'.1) ⧸ s.ker.ideal W') (s.ker.ideal W').Cotangent := hker ▸ h
  have hW' : W' = ⟨U, hUaff⟩ := Subtype.ext U.ι_image_top
  exact (congrArg (fun Z : Y.affineOpens =>
    Module.Finite (Γ(Y, Z.1) ⧸ s.ker.ideal Z) (s.ker.ideal Z).Cotangent ∧
    Module.Projective (Γ(Y, Z.1) ⧸ s.ker.ideal Z) (s.ker.ideal Z).Cotangent) hW') ▸ hW

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Affine.SectionChartConormal.BundleCycles
