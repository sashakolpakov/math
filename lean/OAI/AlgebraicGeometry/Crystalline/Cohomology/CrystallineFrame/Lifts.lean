import OAI.AlgebraicGeometry.Crystalline.Cohomology.AffineFrameCover

/-! # Lifts -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineFrame.Lifts.CrystallineFrameLifts

noncomputable section

/-!
# Coordinate lifts and their changes on the native affine crystalline site

Residue coordinates lift to every actual crystalline ambient ring.
Along a crystalline morphism the discrepancy between chosen lifts lies
in the target PD ideal. These discrepancies satisfy the affine cocycle
identity needed for functorial polynomial linearization.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable (p : ℕ) [Fact p.Prime] (k B σ : Type u) [Field k] [CharP k p]
  [CommRing B] [Algebra k B] (a : σ → B)

local notation "X" => OAI.AlgebraicGeometry.Crystalline.Cohomology.AffineFrameCover.CrystallineAffineFrameCover.affineScheme k B

def lift (Q : Site.Object p k X) (i : σ) : Q.thickening.ring :=
  (Q.thickening.reduction_surjective (AffineFrameCover.CrystallineAffineFrameCover.residualMap p k B Q (a i))).choose

theorem reduction_lift (Q : Site.Object p k X) (i : σ) :
    Q.thickening.reduction (lift p k B σ a Q i) = AffineFrameCover.CrystallineAffineFrameCover.residualMap p k B Q (a i) :=
  (Q.thickening.reduction_surjective (AffineFrameCover.CrystallineAffineFrameCover.residualMap p k B Q (a i))).choose_spec

variable {p k B σ}
variable {Q P U : Site.Object p k (AffineFrameCover.CrystallineAffineFrameCover.affineScheme k B)}

theorem residual_naturality (f : Q ⟶ P) (b : B) :
    AffineFrameCover.CrystallineAffineFrameCover.residualMap p k B Q b =
      f.reducedMap (AffineFrameCover.CrystallineAffineFrameCover.residualMap p k B P b) := by
  have he : CommRingCat.ofHom (AffineFrameCover.CrystallineAffineFrameCover.residualMap p k B Q).toRingHom =
      CommRingCat.ofHom (AffineFrameCover.CrystallineAffineFrameCover.residualMap p k B P).toRingHom ≫
        CommRingCat.ofHom f.reducedMap.toRingHom := by
    apply Spec.map_injective
    rw [Spec.map_comp, AffineFrameCover.CrystallineAffineFrameCover.residualMap_spec,
      AffineFrameCover.CrystallineAffineFrameCover.residualMap_spec]
    exact f.over_X.symm
  exact ConcreteCategory.congr_hom he b

def translation (f : Q ⟶ P) (i : σ) : Q.thickening.ring :=
  lift p k B σ a Q i - f.ambientMap (lift p k B σ a P i)

theorem translation_mem (f : Q ⟶ P) (i : σ) : translation a f i ∈ RingHom.ker Q.thickening.reduction := by
  change Q.thickening.reduction (lift p k B σ a Q i - f.ambientMap (lift p k B σ a P i)) = 0
  rw [map_sub, reduction_lift, f.reduction_comm, reduction_lift, residual_naturality f, sub_self]

theorem translation_id (Q : Site.Object p k X) (i : σ) : translation a (𝟙 Q) i = 0 := by
  change lift p k B σ a Q i - lift p k B σ a Q i = 0
  exact sub_self _

theorem translation_comp (f : Q ⟶ P) (g : P ⟶ U) (i : σ) :
    translation a (f ≫ g) i = translation a f i + f.ambientMap (translation a g i) := by
  change lift p k B σ a Q i - f.ambientMap (g.ambientMap (lift p k B σ a U i)) =
    (lift p k B σ a Q i - f.ambientMap (lift p k B σ a P i)) +
      f.ambientMap (lift p k B σ a P i - g.ambientMap (lift p k B σ a U i))
  rw [map_sub, sub_add_sub_cancel]

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineFrame.Lifts.CrystallineFrameLifts
