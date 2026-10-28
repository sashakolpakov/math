import OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.TwistResolution

/-! # Twist Presheaf Source -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.TwistPresheafSource.BigCrystallineTwistPresheafSource

noncomputable section

/-! # The original structure presheaf under inverse coefficient base twist -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

open OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.FrameLifts.BigCrystallineFrameLifts

universe u

variable (p : ℕ) (W A : Type u) [CommRing W] [CommRing A]
  (J : Ideal W) (δ : DividedPowers J)
  (base base' : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of W))
  (e : W ≃+* W) (he : DividedPowers.IsDPMorphism δ δ e.toRingHom)
  (h : base' = base ≫ Spec.map (CommRingCat.ofHom e.toRingHom))

local notation "C" => OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.FrameLifts.BigCrystallineFrameLifts.Site p W A J δ base
local notation "ι" => OAI.NumberTheory.PadicHodge.PeriodInvariants.CrystallineBaseTwist.twist (p := p) e he h
local notation "F" => OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.TwistResolution.BigCrystallineTwistResolution.restriction p W A J δ base base' e he h
local notation "G" => OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineCohomology.modulePresheaf
  (p := p) (J := J) (δ := δ) base'
local notation "H" => OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineCohomology.modulePresheaf
  (p := p) (J := J) (δ := δ) base

def iso : (F).obj G ≅ H :=
  NatIso.ofComponents (fun Q =>
    { hom := ModuleCat.ofHom
        (X := ((F).obj G).obj Q) (Y := (H).obj Q)
        { toFun := fun x => x
          map_add' := fun _ _ => rfl
          map_smul' := fun b x => by
            change Q.unop.ring at x
            change Q.unop.base (e (e.symm b)) * x = Q.unop.base b * x
            rw [e.apply_symm_apply] }
      inv := ModuleCat.ofHom
        (X := (H).obj Q) (Y := ((F).obj G).obj Q)
        { toFun := fun x => x
          map_add' := fun _ _ => rfl
          map_smul' := fun b x => by
            change Q.unop.ring at x
            change Q.unop.base b * x = Q.unop.base (e (e.symm b)) * x
            rw [e.apply_symm_apply] }
      hom_inv_id := by ext x; rfl
      inv_hom_id := by ext x; rfl }) (by intros; ext x; rfl)

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.TwistPresheafSource.BigCrystallineTwistPresheafSource
