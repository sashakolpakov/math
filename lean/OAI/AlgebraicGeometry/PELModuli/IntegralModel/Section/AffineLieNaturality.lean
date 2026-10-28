import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Affine.SectionLie
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.TangentPointCoefficients

/-! # Affine Lie Naturality -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Section.AffineLieNaturality

noncomputable section

section

/-! The actual tangent map between affine smooth section charts
corresponds to the dual of the actual conormal map. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.AlgebraicGeometry

namespace AffineSectionLie

variable {X Y Z : Scheme.{0}} (p : Y ⟶ X) (p' : Z ⟶ X)
  (s : X ⟶ Y) (s' : X ⟶ Z) {k : Type} [Field k] (q : Spec (.of k) ⟶ X)
  (f : Y ⟶ Z) (hf : f ≫ p' = p) (he : s ≫ f = s')

include he in
theorem zeroPoint_comp : Affine.SectionLie.AffineSectionLie.zeroPoint s q ≫ f = Affine.SectionLie.AffineSectionLie.zeroPoint s' q := by
  dsimp only [Affine.SectionLie.AffineSectionLie.zeroPoint]
  rw [Category.assoc, Category.assoc, he]

def map : Affine.SectionLie.AffineSectionLie.Space p s q →ₗ[k] Affine.SectionLie.AffineSectionLie.Space p' s' q := by
  let m : Affine.SectionLie.AffineSectionLie.Space p s q →ₗ[DualNumber k] Affine.SectionLie.AffineSectionLie.Space p' s' q :=
    Relative.TangentBaseChange.RelativeTangent.map (C := .of (DualNumber k)) (DualNumberReduction.AlgebraicLie.dualIdeal k) (DualNumberReduction.AlgebraicLie.dualIdeal_square k)
      p (Affine.SectionLie.AffineSectionLie.zeroPoint s q) p' (Affine.SectionLie.AffineSectionLie.zeroPoint s' q) f (𝟙 X)
      (hf.trans (Category.comp_id p).symm) (zeroPoint_comp s s' q f he)
  exact m.restrictScalars k

theorem map_germ (v : Affine.SectionLie.AffineSectionLie.Space p s q) (b : Γ(Z, ⊤)) :
    (map p p' s s' q f hf he v).val.hom
        (Z.presheaf.Γgerm ((Affine.SectionLie.AffineSectionLie.zeroPoint s' q) (IsLocalRing.closedPoint (DualNumber k))) b) =
      v.val.hom (Y.presheaf.Γgerm ((Affine.SectionLie.AffineSectionLie.zeroPoint s q) (IsLocalRing.closedPoint (DualNumber k))) (f.appTop b)) :=
  TangentPointCoefficients.RelativeTangent.map_germ (C := .of (DualNumber k)) (DualNumberReduction.AlgebraicLie.dualIdeal k) (DualNumberReduction.AlgebraicLie.dualIdeal_square k)
    p (Affine.SectionLie.AffineSectionLie.zeroPoint s q) p' (Affine.SectionLie.AffineSectionLie.zeroPoint s' q) f (𝟙 X)
    (hf.trans (Category.comp_id p).symm) (zeroPoint_comp s s' q f he) v b

def kernelMap (b : RingHom.ker s'.appTop.hom) : RingHom.ker s.appTop.hom :=
  ⟨f.appTop b.val, by
    change s.appTop (f.appTop b.val) = 0
    exact (ConcreteCategory.congr_hom ((Scheme.Hom.comp_appTop s f).symm.trans
      (congrArg Scheme.Hom.appTop he)) b.val).trans (RingHom.mem_ker.mp b.property)⟩

theorem conormalMap_toCotangent (hs : s ≫ p = 𝟙 X) (hs' : s' ≫ p' = 𝟙 X)
    (b : RingHom.ker s'.appTop.hom) :
    letI := Divisors.LineBundles.Affine.SchemeSection.BundleCycles.AffineSchemeSection.baseAlgebra p
    letI := Divisors.LineBundles.Affine.SchemeSection.BundleCycles.AffineSchemeSection.baseAlgebra p'
    Affine.ConormalRestriction.AffineSectionConormal.map p p' s s' hs hs' f hf he (Ideal.toCotangent _ b) =
      Ideal.toCotangent _ (kernelMap s s' f he b) := rfl

theorem conormalEquiv_natural [IsAffine X] [IsAffine Y] [IsAffine Z] [Smooth p] [Smooth p']
    (hs : s ≫ p = 𝟙 X) (hs' : s' ≫ p' = 𝟙 X) (v : Affine.SectionLie.AffineSectionLie.Space p s q) :
    letI := Divisors.LineBundles.Affine.SchemeSection.BundleCycles.AffineSchemeSection.baseAlgebra p
    letI := Divisors.LineBundles.Affine.SchemeSection.BundleCycles.AffineSchemeSection.baseAlgebra p'
    letI := Affine.SectionLie.AffineSectionLie.baseFieldAlgebra q
    Affine.SectionLie.AffineSectionLie.conormalEquiv p' s' hs' q (map p p' s s' q f hf he v) =
      (Affine.SectionLie.AffineSectionLie.conormalEquiv p s hs q v).comp (Affine.ConormalRestriction.AffineSectionConormal.map p p' s s' hs hs' f hf he) := by
  let := Divisors.LineBundles.Affine.SchemeSection.BundleCycles.AffineSchemeSection.baseAlgebra p
  let := Divisors.LineBundles.Affine.SchemeSection.BundleCycles.AffineSchemeSection.baseAlgebra p'
  let := Affine.SectionLie.AffineSectionLie.baseFieldAlgebra q
  apply LinearMap.ext
  intro b
  obtain ⟨b, rfl⟩ := Ideal.toCotangent_surjective (RingHom.ker s'.appTop.hom) b
  rw [LinearMap.comp_apply, conormalMap_toCotangent, Affine.SectionLie.AffineSectionLie.conormalEquiv_toCotangent, Affine.SectionLie.AffineSectionLie.conormalEquiv_toCotangent]
  exact congrArg TrivSqZeroExt.snd (map_germ p p' s s' q f hf he v b)

end AffineSectionLie

end

/-! Actual scheme points underlying the section Lie module and its maps. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.AlgebraicGeometry

namespace AffineSectionLie

variable {X Y : Scheme.{0}} (p : Y ⟶ X) (s : X ⟶ Y)
  {k : Type} [Field k] (q : Spec (.of k) ⟶ X)

def point (v : Affine.SectionLie.AffineSectionLie.Space p s q) : Spec (.of (DualNumber k)) ⟶ Y :=
  Relative.TangentBaseChange.RelativeTangent.point (C := .of (DualNumber k))
    (DualNumberReduction.AlgebraicLie.dualIdeal k) (DualNumberReduction.AlgebraicLie.dualIdeal_square k) p (Affine.SectionLie.AffineSectionLie.zeroPoint s q) v

theorem point_injective : Function.Injective (point p s q) :=
  Relative.TangentBaseChange.RelativeTangent.point_injective (C := .of (DualNumber k))
    (DualNumberReduction.AlgebraicLie.dualIdeal k) (DualNumberReduction.AlgebraicLie.dualIdeal_square k) p (Affine.SectionLie.AffineSectionLie.zeroPoint s q)

theorem point_map {Z : Scheme.{0}} (p' : Z ⟶ X) (s' : X ⟶ Z)
    (f : Y ⟶ Z) (hf : f ≫ p' = p) (he : s ≫ f = s') (v : Affine.SectionLie.AffineSectionLie.Space p s q) :
    point p' s' q (map p p' s s' q f hf he v) = point p s q v ≫ f :=
  Relative.TangentBaseChange.RelativeTangent.point_map (C := .of (DualNumber k))
    (DualNumberReduction.AlgebraicLie.dualIdeal k) (DualNumberReduction.AlgebraicLie.dualIdeal_square k) p (Affine.SectionLie.AffineSectionLie.zeroPoint s q)
    p' (Affine.SectionLie.AffineSectionLie.zeroPoint s' q) f (𝟙 X) (hf.trans (Category.comp_id p).symm) (zeroPoint_comp s s' q f he) v

end AffineSectionLie

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Section.AffineLieNaturality
