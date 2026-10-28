import OAI.AlgebraicGeometry.Divisors.LineBundles.Affine.SectionChartConormal
import OAI.AlgebraicGeometry.Divisors.LineBundles.Section.QuotientConormalRank
import OAI.AlgebraicGeometry.Divisors.LineBundles.Section.OpenRelativeDimension

/-! # Section Chart Conormal Rank -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Affine.SectionChartConormalRank.BundleCycles

noncomputable section

/-! On the actual affine charts of a smooth closed section, the quotient
conormal module has rank equal to the relative dimension of the projection. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

theorem AffineSchemeSection.conormal_rank {X Y : Scheme.{0}} [IsAffine X] [IsAffine Y]
    (p : Y ⟶ X) [Smooth p] (n : ℕ) [SmoothOfRelativeDimension n p]
    (s : X ⟶ Y) (hs : s ≫ p = 𝟙 X) (q : PrimeSpectrum (Γ(Y, ⊤) ⧸ RingHom.ker s.appTop.hom)) :
    Module.rankAtStalk (R := Γ(Y, ⊤) ⧸ RingHom.ker s.appTop.hom) (RingHom.ker s.appTop.hom).Cotangent q = n := by
  let := SchemeSection.BundleCycles.AffineSchemeSection.baseAlgebra p
  let := SchemeSection.BundleCycles.AffineSchemeSection.quotientAlgebra s
  let := SchemeSection.BundleCycles.AffineSchemeSection.scalarTower p s hs
  let := SchemeSection.BundleCycles.AffineSchemeSection.sectionRing_smooth p
  have hr : RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension n) p.appTop.hom :=
    HasRingHomProperty.appTop (P := @SmoothOfRelativeDimension n) p inferInstance
  exact Section.QuotientConormalRank.BundleCycles.sectionQuotientConormal_rank_of_relativeDimension Γ(X, ⊤) Γ(Y, ⊤) n hr q

theorem affineSectionChart_conormal_rank_of_restrictedDimension {X Y : Scheme.{0}} (p : Y ⟶ X) [Smooth p]
    (n : ℕ) (s : X ⟶ Y) [IsClosedImmersion s] (hs : s ≫ p = 𝟙 X)
    (U : Y.Opens) (V : X.Opens) (hUaff : IsAffineOpen U) (hVaff : IsAffineOpen V)
    (hV : V ≤ s ⁻¹ᵁ U) (hU : U ≤ p ⁻¹ᵁ V)
    (hrel : SmoothOfRelativeDimension n (Section.OpenRestriction.BundleCycles.sectionOpenProjection p U V hU)) :
    ∀ q : PrimeSpectrum (Γ(Y, U) ⧸ s.ker.ideal ⟨U, hUaff⟩),
      Module.rankAtStalk (s.ker.ideal ⟨U, hUaff⟩).Cotangent q = n := by
  let : IsAffine U.toScheme := hUaff
  let : IsAffine V.toScheme := hVaff
  let q := Section.OpenRestriction.BundleCycles.sectionOpenProjection p U V hU
  let t := Section.OpenRestriction.BundleCycles.sectionOpenMap s U V hV
  let : SmoothOfRelativeDimension n q := hrel
  have ht : t ≫ q = 𝟙 V.toScheme := Section.OpenRestriction.BundleCycles.sectionOpen_retraction p s hs U V hV hU
  have h := AffineSchemeSection.conormal_rank q n t ht
  have he : s ⁻¹ᵁ U = V := Section.OpenRestriction.BundleCycles.sectionOpen_preimage p s hs U V hV hU
  let : IsIso (X.homOfLE hV) := by
    change IsIso (X.isoOfEq he.symm).hom
    infer_instance
  let W : U.toScheme.affineOpens := ⟨⊤, isAffineOpen_top U.toScheme⟩
  let W' : Y.affineOpens := ⟨U.ι ''ᵁ W.1, W.2.image_of_isOpenImmersion U.ι⟩
  have hker : RingHom.ker t.appTop.hom = s.ker.ideal W' := by
    have h₁ : RingHom.ker t.appTop.hom = t.ker.ideal W := (Scheme.Hom.ker_apply t W).symm
    have h₂ : t.ker.ideal W = (morphismRestrict s U).ker.ideal W :=
      congrArg (fun K : U.toScheme.IdealSheafData => K.ideal W)
        (Scheme.Hom.ker_comp_of_isIso (X.homOfLE hV) (morphismRestrict s U))
    exact h₁.trans (h₂.trans (Scheme.ker_morphismRestrict_ideal s U W))
  have hW : ∀ a : PrimeSpectrum (Γ(Y, W'.1) ⧸ s.ker.ideal W'),
      Module.rankAtStalk (s.ker.ideal W').Cotangent a = n := hker ▸ h
  have hW' : W' = ⟨U, hUaff⟩ := Subtype.ext U.ι_image_top
  exact (congrArg (fun Z : Y.affineOpens => ∀ a : PrimeSpectrum (Γ(Y, Z.1) ⧸ s.ker.ideal Z),
    Module.rankAtStalk (s.ker.ideal Z).Cotangent a = n) hW') ▸ hW

theorem affineSectionChart_conormal_rank {X Y : Scheme.{0}} (p : Y ⟶ X) [Smooth p]
    (n : ℕ) [SmoothOfRelativeDimension n p] (s : X ⟶ Y) [IsClosedImmersion s] (hs : s ≫ p = 𝟙 X)
    (U : Y.Opens) (V : X.Opens) (hUaff : IsAffineOpen U) (hVaff : IsAffineOpen V)
    (hV : V ≤ s ⁻¹ᵁ U) (hU : U ≤ p ⁻¹ᵁ V) :
    ∀ q : PrimeSpectrum (Γ(Y, U) ⧸ s.ker.ideal ⟨U, hUaff⟩),
      Module.rankAtStalk (s.ker.ideal ⟨U, hUaff⟩).Cotangent q = n :=
  affineSectionChart_conormal_rank_of_restrictedDimension p n s hs U V hUaff hVaff hV hU
    (Section.OpenRelativeDimension.BundleCycles.sectionOpenProjection_relativeDimension p n U V hU)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Affine.SectionChartConormalRank.BundleCycles
