import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Abelian.CoefficientPullback

/-! # Additive Constant Pullback Normalization -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.AdditiveConstantPullbackNormalization

noncomputable section

section

/-! Morphisms from the actual constant integer sheaf are exactly
global sections, with the original section maps as their coefficient action. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite

variable {X : TopCat.{0}}

def additiveHomTopSectionsEquiv (F : ArithmeticGeometry.OrdinaryLocus.Openness.AbelianSheafInjectives.Construction.AbelianSheaves X) :
    (Abelian.CoefficientPullback.additiveConstantZ X ⟶ F) ≃+ F.obj.obj (op ⊤) :=
  ((constantSheafAdj (_root_.Opens.grothendieckTopology X) AddCommGrpCat.{0}
    isTerminalTop).homAddEquiv (AddCommGrpCat.of (ULift ℤ)) F).trans
      (AddCommGrpCat.uliftZMultiplesAddEquiv _)

theorem additiveHomTopSectionsEquiv_natural {F G : ArithmeticGeometry.OrdinaryLocus.Openness.AbelianSheafInjectives.Construction.AbelianSheaves X}
    (z : Abelian.CoefficientPullback.additiveConstantZ X ⟶ F) (a : F ⟶ G) :
    additiveHomTopSectionsEquiv G (z ≫ a) =
      a.hom.app (op ⊤) (additiveHomTopSectionsEquiv F z) := by
  let adj := constantSheafAdj (_root_.Opens.grothendieckTopology X) AddCommGrpCat.{0}
    isTerminalTop
  change AddCommGrpCat.uliftZMultiplesAddEquiv _ (adj.homEquiv _ _ (z ≫ a)) = _
  rw [adj.homEquiv_naturality_right]
  rfl

theorem additiveHomTopSectionsEquiv_symm_natural {F G : ArithmeticGeometry.OrdinaryLocus.Openness.AbelianSheafInjectives.Construction.AbelianSheaves X}
    (s : F.obj.obj (op ⊤)) (a : F ⟶ G) :
    (additiveHomTopSectionsEquiv F).symm s ≫ a =
      (additiveHomTopSectionsEquiv G).symm (a.hom.app (op ⊤) s) := by
  apply (additiveHomTopSectionsEquiv G).injective
  rw [additiveHomTopSectionsEquiv_natural, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]

end

/-! The constant-sheaf isomorphism in native Ext pullback agrees with
the original direct-image map on global sections. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite

variable {X Y : TopCat.{0}} (f : X ⟶ Y)

theorem additivePullbackConstantIso_homEquiv (G : ArithmeticGeometry.OrdinaryLocus.Openness.AbelianSheafInjectives.Construction.AbelianSheaves X)
    (z : Abelian.CoefficientPullback.additiveConstantZ X ⟶ G) :
    (constantSheafAdj (_root_.Opens.grothendieckTopology Y) AddCommGrpCat.{0} isTerminalTop).homEquiv
        (AddCommGrpCat.of (ULift ℤ)) ((ArithmeticGeometry.OrdinaryLocus.Openness.AbelianSheafPullback.Construction.abelianSheafPushforward f).obj G)
        ((ArithmeticGeometry.OrdinaryLocus.Openness.AbelianSheafPullback.Construction.abelianSheafPullbackAdjunction f).homEquiv _ _
          (((ArithmeticGeometry.OrdinaryLocus.Openness.PushforwardCohomology.Construction.abelianPullbackConstantIso f).app (AddCommGrpCat.of (ULift ℤ))).hom ≫ z)) =
      (constantSheafAdj (_root_.Opens.grothendieckTopology X) AddCommGrpCat.{0} isTerminalTop).homEquiv
        (AddCommGrpCat.of (ULift ℤ)) G z := by
  let a := constantSheafAdj (_root_.Opens.grothendieckTopology Y) AddCommGrpCat.{0} isTerminalTop
  let b := ArithmeticGeometry.OrdinaryLocus.Openness.AbelianSheafPullback.Construction.abelianSheafPullbackAdjunction f
  let c := constantSheafAdj (_root_.Opens.grothendieckTopology X) AddCommGrpCat.{0} isTerminalTop
  let e := (ArithmeticGeometry.OrdinaryLocus.Openness.PushforwardCohomology.Construction.abelianPullbackConstantIso f).app (AddCommGrpCat.of (ULift ℤ))
  change (a.comp b).homEquiv _ _ (e.hom ≫ z) = c.homEquiv _ _ z
  rw [Adjunction.homEquiv_naturality_right]
  have h : (a.comp b).homEquiv _ _ e.hom = c.unit.app (AddCommGrpCat.of (ULift ℤ)) :=
    Adjunction.homEquiv_leftAdjointUniq_hom_app (a.comp b) c (AddCommGrpCat.of (ULift ℤ))
  rw [h, Adjunction.homEquiv_unit]
  rfl

theorem additiveHomTopSectionsEquiv_adjoint (G : ArithmeticGeometry.OrdinaryLocus.Openness.AbelianSheafInjectives.Construction.AbelianSheaves X)
    (z : Abelian.CoefficientPullback.additiveConstantZ Y ⟶ (ArithmeticGeometry.OrdinaryLocus.Openness.AbelianSheafPullback.Construction.abelianSheafPushforward f).obj G) :
    additiveHomTopSectionsEquiv G
        (((ArithmeticGeometry.OrdinaryLocus.Openness.PushforwardCohomology.Construction.abelianPullbackConstantIso f).app (AddCommGrpCat.of (ULift ℤ))).inv ≫
          ((ArithmeticGeometry.OrdinaryLocus.Openness.AbelianSheafPullback.Construction.abelianSheafPullbackAdjunction f).homEquiv _ _).symm z) =
      additiveHomTopSectionsEquiv ((ArithmeticGeometry.OrdinaryLocus.Openness.AbelianSheafPullback.Construction.abelianSheafPushforward f).obj G) z := by
  let e := (ArithmeticGeometry.OrdinaryLocus.Openness.PushforwardCohomology.Construction.abelianPullbackConstantIso f).app (AddCommGrpCat.of (ULift ℤ))
  let adj := ArithmeticGeometry.OrdinaryLocus.Openness.AbelianSheafPullback.Construction.abelianSheafPullbackAdjunction f
  have h := additivePullbackConstantIso_homEquiv f G (e.inv ≫ (adj.homEquiv _ _).symm z)
  rw [e.hom_inv_id_assoc, Equiv.apply_symm_apply] at h
  exact (congrArg (AddCommGrpCat.uliftZMultiplesAddEquiv _) h).symm

theorem additiveHomTopSectionsEquiv_coefficientPullback
    {F : ArithmeticGeometry.OrdinaryLocus.Openness.AbelianSheafInjectives.Construction.AbelianSheaves Y} {G : ArithmeticGeometry.OrdinaryLocus.Openness.AbelianSheafInjectives.Construction.AbelianSheaves X}
    (a : F ⟶ (ArithmeticGeometry.OrdinaryLocus.Openness.AbelianSheafPullback.Construction.abelianSheafPushforward f).obj G) (z : Abelian.CoefficientPullback.additiveConstantZ Y ⟶ F) :
    additiveHomTopSectionsEquiv G
        (((ArithmeticGeometry.OrdinaryLocus.Openness.PushforwardCohomology.Construction.abelianPullbackConstantIso f).app (AddCommGrpCat.of (ULift ℤ))).inv ≫
          (ArithmeticGeometry.OrdinaryLocus.Openness.AbelianSheafPullback.Construction.abelianSheafPullback f).map z ≫ ((ArithmeticGeometry.OrdinaryLocus.Openness.AbelianSheafPullback.Construction.abelianSheafPullbackAdjunction f).homEquiv F G).symm a) =
      a.hom.app (op ⊤) (additiveHomTopSectionsEquiv F z) := by
  have h := additiveHomTopSectionsEquiv_adjoint f G (z ≫ a)
  rw [Adjunction.homEquiv_naturality_left_symm, additiveHomTopSectionsEquiv_natural] at h
  exact h

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.AdditiveConstantPullbackNormalization
