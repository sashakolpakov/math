import OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite

/-! # Frame Lifts -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.FrameLifts.BigCrystallineFrameLifts

noncomputable section

/-! # Coordinate lifts on the original big affine crystalline site

The residual map to the affine scheme is arbitrary. Chosen lifts differ
along a crystalline morphism by elements of its actual PD ideal, and
these differences obey the affine cocycle identity.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite

universe u

variable (p : ℕ) (W A σ : Type u) [CommRing W] [CommRing A]
  (J : Ideal W) (δ : DividedPowers J) (base : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of W)) (a : σ → A)

abbrev Site := NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite.Object p W J δ base

instance baseAlgebra (U : Site p W A J δ base) : Algebra W U.ring := U.base.toAlgebra

def residualMap (U : Site p W A J δ base) : A →+* U.ring ⧸ U.ideal :=
  (Spec.preimage U.mapToX).hom

theorem residualMap_spec (U : Site p W A J δ base) :
    Spec.map (CommRingCat.ofHom (residualMap p W A J δ base U)) = U.mapToX :=
  Spec.map_preimage _

def lift (U : Site p W A J δ base) (i : σ) : U.ring :=
  (Ideal.Quotient.mk_surjective (residualMap p W A J δ base U (a i))).choose

theorem reduction_lift (U : Site p W A J δ base) (i : σ) :
    Ideal.Quotient.mk U.ideal (lift p W A σ J δ base a U i) = residualMap p W A J δ base U (a i) :=
  (Ideal.Quotient.mk_surjective (residualMap p W A J δ base U (a i))).choose_spec

variable {p W A σ J δ base}
variable {U V T : Site p W A J δ base}

theorem residual_naturality (f : U ⟶ V) (b : A) :
    residualMap p W A J δ base U b = NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite.Object.quotientMap U V f.ringMap (residualMap p W A J δ base V b) := by
  have he : CommRingCat.ofHom (residualMap p W A J δ base U) =
      CommRingCat.ofHom (residualMap p W A J δ base V) ≫
        CommRingCat.ofHom (NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite.Object.quotientMap U V f.ringMap) := by
    apply Spec.map_injective
    rw [Spec.map_comp, residualMap_spec, residualMap_spec]
    exact f.overX.symm
  exact ConcreteCategory.congr_hom he b

def translation (f : U ⟶ V) (i : σ) : U.ring :=
  lift p W A σ J δ base a U i - f.ringMap.toRingHom (lift p W A σ J δ base a V i)

theorem translation_mem (f : U ⟶ V) (i : σ) : translation a f i ∈ U.ideal := by
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  change Ideal.Quotient.mk U.ideal
    (lift p W A σ J δ base a U i - f.ringMap.toRingHom (lift p W A σ J δ base a V i)) = 0
  rw [map_sub, reduction_lift]
  change residualMap p W A J δ base U (a i) -
    NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite.Object.quotientMap U V f.ringMap
      (Ideal.Quotient.mk V.ideal (lift p W A σ J δ base a V i)) = 0
  rw [reduction_lift, residual_naturality f, sub_self]

theorem translation_id (U : Site p W A J δ base) (i : σ) : translation a (𝟙 U) i = 0 := by
  change lift p W A σ J δ base a U i - lift p W A σ J δ base a U i = 0
  exact sub_self _

theorem translation_comp (f : U ⟶ V) (g : V ⟶ T) (i : σ) :
    translation a (f ≫ g) i = translation a f i + f.ringMap.toRingHom (translation a g i) := by
  change lift p W A σ J δ base a U i - f.ringMap.toRingHom (g.ringMap.toRingHom (lift p W A σ J δ base a T i)) =
    (lift p W A σ J δ base a U i - f.ringMap.toRingHom (lift p W A σ J δ base a V i)) +
      f.ringMap.toRingHom (lift p W A σ J δ base a V i - g.ringMap.toRingHom (lift p W A σ J δ base a T i))
  rw [map_sub, sub_add_sub_cancel]

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.FrameLifts.BigCrystallineFrameLifts
