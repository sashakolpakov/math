import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Abelian.CoefficientPullback
import OAI.AlgebraicGeometry.Comparison.Betti.Complex.Adjunction

/-! # Resolution Image -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Abelian.ResolutionImage

noncomputable section

/-! The constructed inverse-image comparison has an actual adjoint
map of direct-image resolutions, normalized by the original sheaf map. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

variable {X Y : TopCat.{0}} (f : X ⟶ Y)

local instance resolutionDirectImage_additive : (ArithmeticGeometry.OrdinaryLocus.Openness.AbelianSheafPullback.Construction.abelianSheafPushforward f).Additive where
  map_add := by intros; rfl

variable {F : ArithmeticGeometry.OrdinaryLocus.Openness.AbelianSheafInjectives.Construction.AbelianSheaves Y} {G : ArithmeticGeometry.OrdinaryLocus.Openness.AbelianSheafInjectives.Construction.AbelianSheaves X}
    (a : F ⟶ (ArithmeticGeometry.OrdinaryLocus.Openness.AbelianSheafPullback.Construction.abelianSheafPushforward f).obj G)
    (I : InjectiveResolution F) (J : InjectiveResolution G)

def abelianResolutionDirectImageMap :
    I.cocomplex ⟶ ((ArithmeticGeometry.OrdinaryLocus.Openness.AbelianSheafPullback.Construction.abelianSheafPushforward f).mapHomologicalComplex (.up ℕ)).obj J.cocomplex :=
  (Comparison.Betti.Complex.Adjunction.onComplexes (ArithmeticGeometry.OrdinaryLocus.Openness.AbelianSheafPullback.Construction.abelianSheafPullbackAdjunction f) (.up ℕ)).homEquiv
    I.cocomplex J.cocomplex (CoefficientPullback.abelianCoefficientResolutionPullback f a I J)

theorem abelianResolutionDirectImageMap_f (n : ℕ) :
    (abelianResolutionDirectImageMap f a I J).f n =
      (ArithmeticGeometry.OrdinaryLocus.Openness.AbelianSheafPullback.Construction.abelianSheafPullbackAdjunction f).homEquiv (I.cocomplex.X n) (J.cocomplex.X n)
        ((CoefficientPullback.abelianCoefficientResolutionPullback f a I J).f n) := rfl

theorem abelianResolutionDirectImageMap_zero :
    I.ι.f 0 ≫ (abelianResolutionDirectImageMap f a I J).f 0 =
      a ≫ (ArithmeticGeometry.OrdinaryLocus.Openness.AbelianSheafPullback.Construction.abelianSheafPushforward f).map (J.ι.f 0) := by
  let adj := ArithmeticGeometry.OrdinaryLocus.Openness.AbelianSheafPullback.Construction.abelianSheafPullbackAdjunction f
  let p : (ArithmeticGeometry.OrdinaryLocus.Openness.AbelianSheafPullback.Construction.abelianSheafPullback f).obj (I.cocomplex.X 0) ⟶ J.cocomplex.X 0 :=
    (CoefficientPullback.abelianCoefficientResolutionPullback f a I J).f 0
  have h₁ := adj.homEquiv_naturality_left (I.ι.f 0) p
  have h₂ := congrArg (adj.homEquiv F (J.cocomplex.X 0))
    (CoefficientPullback.abelianCoefficientResolutionPullback_zero f a I J)
  have h₃ := adj.homEquiv_naturality_right ((adj.homEquiv F G).symm a) (J.ι.f 0)
  exact h₁.symm.trans (h₂.trans (h₃.trans
    (congrArg (fun t => t ≫ (ArithmeticGeometry.OrdinaryLocus.Openness.AbelianSheafPullback.Construction.abelianSheafPushforward f).map (J.ι.f 0))
      ((adj.homEquiv F G).apply_symm_apply a))))

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Abelian.ResolutionImage
