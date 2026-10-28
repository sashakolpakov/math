import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Local.CoefficientLieConormal
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.TangentPointCoefficients

/-! # Coefficient Lie Naturality -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Local.CoefficientLieNaturality.LocalCoefficientLie

noncomputable section

/-! Maps between the actual affine section charts commute with the
local-coefficient conormal comparison. The underlying infinitesimal
scheme point is carried by the original scheme morphism. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {X Y Z : Scheme.{0}} (p : Y ⟶ X) (p' : Z ⟶ X)
  (s : X ⟶ Y) (s' : X ⟶ Z) {C : Type} [CommRing C] [IsLocalRing C]
  (q : Spec (.of C) ⟶ X) (f : Y ⟶ Z) (hf : f ≫ p' = p) (he : s ≫ f = s')

omit [IsLocalRing C] in
include he in
theorem zeroPoint_comp : CoefficientLieSpace.LocalCoefficientLie.zeroPoint s q ≫ f = CoefficientLieSpace.LocalCoefficientLie.zeroPoint s' q := by
  dsimp only [CoefficientLieSpace.LocalCoefficientLie.zeroPoint]
  rw [Category.assoc, he]

def map : CoefficientLieSpace.LocalCoefficientLie.Space p s q →ₗ[C] CoefficientLieSpace.LocalCoefficientLie.Space p' s' q := by
  let m : CoefficientLieSpace.LocalCoefficientLie.Space p s q →ₗ[DualNumber C] CoefficientLieSpace.LocalCoefficientLie.Space p' s' q :=
    PELModuli.IntegralModel.Relative.TangentBaseChange.RelativeTangent.map (C := .of (DualNumber C)) (Dual.AlgebraLiftCoordinates.DualCoefficientLifts.ideal C)
      (Dual.AlgebraLiftCoordinates.DualCoefficientLifts.ideal_square C) p (CoefficientLieSpace.LocalCoefficientLie.zeroPoint s q) p' (CoefficientLieSpace.LocalCoefficientLie.zeroPoint s' q) f (𝟙 X)
      (hf.trans (Category.comp_id p).symm) (zeroPoint_comp s s' q f he)
  exact m.restrictScalars C

theorem map_germ (v : CoefficientLieSpace.LocalCoefficientLie.Space p s q) (b : Γ(Z, ⊤)) :
    (map p p' s s' q f hf he v).val.hom
        (Z.presheaf.Γgerm ((CoefficientLieSpace.LocalCoefficientLie.zeroPoint s' q) (IsLocalRing.closedPoint (DualNumber C))) b) =
      v.val.hom (Y.presheaf.Γgerm ((CoefficientLieSpace.LocalCoefficientLie.zeroPoint s q) (IsLocalRing.closedPoint (DualNumber C))) (f.appTop b)) :=
  PELModuli.IntegralModel.TangentPointCoefficients.RelativeTangent.map_germ (C := .of (DualNumber C)) (Dual.AlgebraLiftCoordinates.DualCoefficientLifts.ideal C)
    (Dual.AlgebraLiftCoordinates.DualCoefficientLifts.ideal_square C) p (CoefficientLieSpace.LocalCoefficientLie.zeroPoint s q) p' (CoefficientLieSpace.LocalCoefficientLie.zeroPoint s' q) f (𝟙 X)
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
    PELModuli.IntegralModel.Affine.ConormalRestriction.AffineSectionConormal.map p p' s s' hs hs' f hf he (Ideal.toCotangent _ b) =
      Ideal.toCotangent _ (kernelMap s s' f he b) := rfl

theorem conormalEquiv_natural [IsAffine X] [IsAffine Y] [IsAffine Z] [Smooth p] [Smooth p']
    (hs : s ≫ p = 𝟙 X) (hs' : s' ≫ p' = 𝟙 X) (v : CoefficientLieSpace.LocalCoefficientLie.Space p s q) :
    letI := Divisors.LineBundles.Affine.SchemeSection.BundleCycles.AffineSchemeSection.baseAlgebra p
    letI := Divisors.LineBundles.Affine.SchemeSection.BundleCycles.AffineSchemeSection.baseAlgebra p'
    letI := CoefficientLieSpace.LocalCoefficientLie.baseCoefficientAlgebra q
    CoefficientLieConormal.LocalCoefficientLie.conormalEquiv p' s' hs' q (map p p' s s' q f hf he v) =
      (CoefficientLieConormal.LocalCoefficientLie.conormalEquiv p s hs q v).comp (PELModuli.IntegralModel.Affine.ConormalRestriction.AffineSectionConormal.map p p' s s' hs hs' f hf he) := by
  let := Divisors.LineBundles.Affine.SchemeSection.BundleCycles.AffineSchemeSection.baseAlgebra p
  let := Divisors.LineBundles.Affine.SchemeSection.BundleCycles.AffineSchemeSection.baseAlgebra p'
  let := CoefficientLieSpace.LocalCoefficientLie.baseCoefficientAlgebra q
  apply LinearMap.ext
  intro b
  obtain ⟨b, rfl⟩ := Ideal.toCotangent_surjective (RingHom.ker s'.appTop.hom) b
  rw [LinearMap.comp_apply, conormalMap_toCotangent, CoefficientLieConormal.LocalCoefficientLie.conormalEquiv_toCotangent, CoefficientLieConormal.LocalCoefficientLie.conormalEquiv_toCotangent]
  exact congrArg TrivSqZeroExt.snd (map_germ p p' s s' q f hf he v b)

def point (v : CoefficientLieSpace.LocalCoefficientLie.Space p s q) : Spec (.of (DualNumber C)) ⟶ Y :=
  PELModuli.IntegralModel.Relative.TangentBaseChange.RelativeTangent.point (C := .of (DualNumber C)) (Dual.AlgebraLiftCoordinates.DualCoefficientLifts.ideal C)
    (Dual.AlgebraLiftCoordinates.DualCoefficientLifts.ideal_square C) p (CoefficientLieSpace.LocalCoefficientLie.zeroPoint s q) v

theorem point_injective : Function.Injective (point p s q) :=
  PELModuli.IntegralModel.Relative.TangentBaseChange.RelativeTangent.point_injective (C := .of (DualNumber C)) (Dual.AlgebraLiftCoordinates.DualCoefficientLifts.ideal C)
    (Dual.AlgebraLiftCoordinates.DualCoefficientLifts.ideal_square C) p (CoefficientLieSpace.LocalCoefficientLie.zeroPoint s q)

theorem point_map (v : CoefficientLieSpace.LocalCoefficientLie.Space p s q) :
    point p' s' q (map p p' s s' q f hf he v) = point p s q v ≫ f :=
  PELModuli.IntegralModel.Relative.TangentBaseChange.RelativeTangent.point_map (C := .of (DualNumber C)) (Dual.AlgebraLiftCoordinates.DualCoefficientLifts.ideal C)
    (Dual.AlgebraLiftCoordinates.DualCoefficientLifts.ideal_square C) p (CoefficientLieSpace.LocalCoefficientLie.zeroPoint s q) p' (CoefficientLieSpace.LocalCoefficientLie.zeroPoint s' q) f (𝟙 X)
    (hf.trans (Category.comp_id p).symm) (zeroPoint_comp s s' q f he) v

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Local.CoefficientLieNaturality.LocalCoefficientLie
