import OAI.AlgebraicGeometry.Divisors.LineBundles.EqualRingImages
import OAI.AlgebraicGeometry.Divisors.LineBundles.ValuativeCenterPoint

/-! # Separated Stalk Images -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.SeparatedStalkImages.BundleCycles

noncomputable section

/-! On a separated integral scheme, a point is determined by its actual
local ring embedded in the function field. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable {X : Scheme} [IsIntegral X]

def genericStalkApproach (x : X) : Spec X.functionField ⟶ Spec (X.presheaf.stalk x) :=
  Spec.map (CommRingCat.ofHom (algebraMap (X.presheaf.stalk x) X.functionField))

instance genericStalkApproach_isDominant (x : X) : IsDominant (genericStalkApproach x) := by
  refine ⟨?_⟩
  change DenseRange (PrimeSpectrum.comap (algebraMap (X.presheaf.stalk x) X.functionField))
  rw [PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical,
    (RingHom.injective_iff_ker_eq_bot _).mp (IsFractionRing.injective (X.presheaf.stalk x) X.functionField)]
  exact bot_le

theorem genericStalkApproach_fromSpecStalk (x : X) :
    genericStalkApproach x ≫ X.fromSpecStalk x = IntersectionTheory.ProjectionFormula.Normalization.Scheme.genericMap X := by
  change Spec.map (X.presheaf.stalkSpecializes ((genericPoint_spec X).specializes trivial)) ≫
    X.fromSpecStalk x = _
  exact Scheme.SpecMap_stalkSpecializes_fromSpecStalk ((genericPoint_spec X).specializes trivial)

theorem point_eq_of_stalkImages_eq [X.IsSeparated] (x y : X)
    (h : (algebraMap (X.presheaf.stalk x) X.functionField).range =
      (algebraMap (X.presheaf.stalk y) X.functionField).range) : x = y := by
  let e := EqualRingImages.BundleCycles.equalRingImagesEquiv (algebraMap (X.presheaf.stalk x) X.functionField)
    (algebraMap (X.presheaf.stalk y) X.functionField)
    (IsFractionRing.injective _ _) (IsFractionRing.injective _ _) h
  have he : e.toCommRingCatIso.hom ≫
      CommRingCat.ofHom (algebraMap (X.presheaf.stalk y) X.functionField) =
        CommRingCat.ofHom (algebraMap (X.presheaf.stalk x) X.functionField) := by
    ext r
    exact EqualRingImages.BundleCycles.equalRingImagesEquiv_apply _ _ _ _ h r
  have hg : genericStalkApproach y ≫
      (Spec.map e.toCommRingCatIso.hom ≫ X.fromSpecStalk x) =
        genericStalkApproach y ≫ X.fromSpecStalk y := by
    change Spec.map (CommRingCat.ofHom (algebraMap (X.presheaf.stalk y) X.functionField)) ≫
      (Spec.map e.toCommRingCatIso.hom ≫ X.fromSpecStalk x) = _
    rw [← Spec.map_comp_assoc, he]
    exact (genericStalkApproach_fromSpecStalk x).trans (genericStalkApproach_fromSpecStalk y).symm
  have hs := ext_of_isDominant (genericStalkApproach y) hg
  have hx := congrArg (fun s : Spec (X.presheaf.stalk y) ⟶ X =>
    s (IsLocalRing.closedPoint (X.presheaf.stalk y))) hs
  change X.fromSpecStalk x (Spec.map e.toCommRingCatIso.hom
    (IsLocalRing.closedPoint (X.presheaf.stalk y))) =
      X.fromSpecStalk y (IsLocalRing.closedPoint (X.presheaf.stalk y)) at hx
  simpa only [Spec_closedPoint, Scheme.fromSpecStalk_closedPoint] using hx

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.SeparatedStalkImages.BundleCycles
