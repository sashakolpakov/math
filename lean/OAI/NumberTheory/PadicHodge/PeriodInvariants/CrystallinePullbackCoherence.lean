import OAI.NumberTheory.PadicHodge.PeriodInvariants.CrystallineSheafCoherence
import OAI.NumberTheory.PadicHodge.PeriodInvariants.CrystallinePullback

/-! # Crystalline Pullback Coherence -/

namespace OAI.NumberTheory.PadicHodge.PeriodInvariants.CrystallinePullbackCoherence

noncomputable section

/-!
# Identity and composition for actual crystalline cohomology pullback

Coherent exact restriction induces coherent maps on the actual Ext groups.
The big-to-small comparison and scalar extension carry these laws to the
integral and rational crystalline cohomology used by PeriodInvariants.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped TensorProduct

universe u

namespace Big

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineCohomology
  CrystallineRestrictionCoherence CrystallineSheafCoherence ExtTransport

variable {p : ℕ} {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
variable {X Y Z : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of B)}
  {fY : Y ⟶ Spec (CommRingCat.of B)} {fZ : Z ⟶ Spec (CommRingCat.of B)}

theorem pullback_id (n : ℕ) (x : IntegralComparison.BigCrystallineCohomology.Cohomology (p := p) (J := J) (δ := δ) f n) :
    IntegralComparison.BigCrystallineCohomology.pullback (𝟙 X) (Category.id_comp f) n x = x := by
  change ExtTransport.exactTransport (IntegralComparison.Crystalline.ExactRestriction.Coeff (B := B)) (IntegralComparison.Crystalline.ExactRestriction.restriction (𝟙 X) (Category.id_comp f))
    (IntegralComparison.BigCrystallineCohomology.constantTransport (𝟙 X) (Category.id_comp f)) (IntegralComparison.BigCrystallineCohomology.structureTransport (𝟙 X) (Category.id_comp f)) n x = x
  rw [CrystallineSheafCoherence.constantTransport_id, CrystallineSheafCoherence.structureTransport_id]
  have hn := ExtTransport.exactTransport_natIso (IntegralComparison.Crystalline.ExactRestriction.Coeff (B := B)) CrystallineRestrictionCoherence.restrictionId
    (Iso.refl (IntegralComparison.BigCrystallineCohomology.constantUnit f)) (Iso.refl (IntegralComparison.BigCrystallineCohomology.structureSheaf f)) x
  have ht := congrArg₂ (fun iA iB => ExtTransport.exactTransport (IntegralComparison.Crystalline.ExactRestriction.Coeff (B := B))
    (IntegralComparison.Crystalline.ExactRestriction.restriction (𝟙 X) (Category.id_comp f)) iA iB n x)
    (Iso.trans_refl (CrystallineRestrictionCoherence.restrictionId.app (IntegralComparison.BigCrystallineCohomology.constantUnit f))).symm
    (Iso.trans_refl (CrystallineRestrictionCoherence.restrictionId.app (IntegralComparison.BigCrystallineCohomology.structureSheaf f))).symm
  exact ht.trans (hn.trans (ExtTransport.exactTransport_id (IntegralComparison.Crystalline.ExactRestriction.Coeff (B := B)) x))

theorem pullback_comp (g : X ⟶ Y) (hg : g ≫ fY = f) (h : Y ⟶ Z) (hh : h ≫ fZ = fY)
    (n : ℕ) (x : IntegralComparison.BigCrystallineCohomology.Cohomology (p := p) (J := J) (δ := δ) fZ n) :
    IntegralComparison.BigCrystallineCohomology.pullback g hg n (IntegralComparison.BigCrystallineCohomology.pullback h hh n x) = IntegralComparison.BigCrystallineCohomology.pullback (g ≫ h) (CrystallineRestrictionCoherence.composite_over g hg h hh) n x := by
  change ExtTransport.exactTransport (IntegralComparison.Crystalline.ExactRestriction.Coeff (B := B)) (IntegralComparison.Crystalline.ExactRestriction.restriction g hg) (IntegralComparison.BigCrystallineCohomology.constantTransport g hg)
    (IntegralComparison.BigCrystallineCohomology.structureTransport g hg) n
    (ExtTransport.exactTransport (IntegralComparison.Crystalline.ExactRestriction.Coeff (B := B)) (IntegralComparison.Crystalline.ExactRestriction.restriction h hh) (IntegralComparison.BigCrystallineCohomology.constantTransport h hh)
      (IntegralComparison.BigCrystallineCohomology.structureTransport h hh) n x) =
    ExtTransport.exactTransport (IntegralComparison.Crystalline.ExactRestriction.Coeff (B := B)) (IntegralComparison.Crystalline.ExactRestriction.restriction (g ≫ h) (CrystallineRestrictionCoherence.composite_over g hg h hh))
      (IntegralComparison.BigCrystallineCohomology.constantTransport (g ≫ h) (CrystallineRestrictionCoherence.composite_over g hg h hh))
      (IntegralComparison.BigCrystallineCohomology.structureTransport (g ≫ h) (CrystallineRestrictionCoherence.composite_over g hg h hh)) n x
  rw [ExtTransport.exactTransport_comp, CrystallineSheafCoherence.constantTransport_comp, CrystallineSheafCoherence.structureTransport_comp]
  exact ExtTransport.exactTransport_natIso (IntegralComparison.Crystalline.ExactRestriction.Coeff (B := B)) (CrystallineRestrictionCoherence.restrictionComp g hg h hh)
    (IntegralComparison.BigCrystallineCohomology.constantTransport (g ≫ h) (CrystallineRestrictionCoherence.composite_over g hg h hh))
    (IntegralComparison.BigCrystallineCohomology.structureTransport (g ≫ h) (CrystallineRestrictionCoherence.composite_over g hg h hh)) x

end Big

open OAI.NumberTheory.PadicHodge.PeriodInvariants.CrystallinePullback OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline OAI.NumberTheory.PadicHodge.IntegralComparison.Global.Crystalline.Comparison

variable (p : ℕ) [Fact p.Prime]
variable (k : Type u) [Field k] [CharP k p]
variable {X Y Z : Over (Spec (CommRingCat.of k))}

theorem bigPullback_id (X : Over (Spec (CommRingCat.of k))) (n : ℕ)
    (x : CrystallinePullback.BigCohomology p k X n) : CrystallinePullback.bigPullback p k (𝟙 X) n x = x :=
  Big.pullback_id n x

theorem bigPullback_comp (g : X ⟶ Y) (h : Y ⟶ Z) (n : ℕ) (x : CrystallinePullback.BigCohomology p k Z n) :
    CrystallinePullback.bigPullback p k g n (CrystallinePullback.bigPullback p k h n x) = CrystallinePullback.bigPullback p k (g ≫ h) n x :=
  Big.pullback_comp g.left (CrystallinePullback.over_witt p k g) h.left (CrystallinePullback.over_witt p k h) n x

variable [IsSeparated X.hom] [IsSeparated Y.hom] [IsSeparated Z.hom]

omit Y Z [IsSeparated Y.hom] [IsSeparated Z.hom] in
theorem integralPullback_id (n : ℕ) (x : IntegralComparison.Witt.Crystalline.integralCohomology p k X n) :
    CrystallinePullback.integralPullback p k (𝟙 X) n x = x := by
  change IntegralComparison.Global.Crystalline.Comparison.integralEquivWitt p k X n (CrystallinePullback.bigPullback p k (𝟙 X) n ((IntegralComparison.Global.Crystalline.Comparison.integralEquivWitt p k X n).symm x)) = x
  rw [bigPullback_id, LinearEquiv.apply_symm_apply]

theorem integralPullback_comp (g : X ⟶ Y) (h : Y ⟶ Z) (n : ℕ)
    (x : IntegralComparison.Witt.Crystalline.integralCohomology p k Z n) :
    CrystallinePullback.integralPullback p k g n (CrystallinePullback.integralPullback p k h n x) = CrystallinePullback.integralPullback p k (g ≫ h) n x := by
  change IntegralComparison.Global.Crystalline.Comparison.integralEquivWitt p k X n (CrystallinePullback.bigPullback p k g n ((IntegralComparison.Global.Crystalline.Comparison.integralEquivWitt p k Y n).symm
    (IntegralComparison.Global.Crystalline.Comparison.integralEquivWitt p k Y n (CrystallinePullback.bigPullback p k h n ((IntegralComparison.Global.Crystalline.Comparison.integralEquivWitt p k Z n).symm x))))) =
    IntegralComparison.Global.Crystalline.Comparison.integralEquivWitt p k X n (CrystallinePullback.bigPullback p k (g ≫ h) n ((IntegralComparison.Global.Crystalline.Comparison.integralEquivWitt p k Z n).symm x))
  rw [LinearEquiv.symm_apply_apply, bigPullback_comp]

omit Y Z [IsSeparated Y.hom] [IsSeparated Z.hom] in
theorem rationalPullback_id (n : ℕ) (x : IntegralComparison.Witt.Crystalline.rationalCohomology p k X n) :
    CrystallinePullback.rationalPullback p k (𝟙 X) n x = x := by
  induction x using TensorProduct.inductionOn with
  | tmul a x => exact congrArg (fun z => a ⊗ₜ[WittVector p k] z) (integralPullback_id p k n x)
  | add x y hx hy =>
    exact ((CrystallinePullback.rationalPullback p k (𝟙 X) n).map_add x y).trans (congrArg₂ (fun a b => a + b) hx hy)

theorem rationalPullback_comp (g : X ⟶ Y) (h : Y ⟶ Z) (n : ℕ)
    (x : IntegralComparison.Witt.Crystalline.rationalCohomology p k Z n) :
    CrystallinePullback.rationalPullback p k g n (CrystallinePullback.rationalPullback p k h n x) = CrystallinePullback.rationalPullback p k (g ≫ h) n x := by
  induction x using TensorProduct.inductionOn with
  | tmul a x => exact congrArg (fun z => a ⊗ₜ[WittVector p k] z) (integralPullback_comp p k g h n x)
  | add x y hx hy =>
    exact (congrArg (CrystallinePullback.rationalPullback p k g n) ((CrystallinePullback.rationalPullback p k h n).map_add x y)).trans
      (((CrystallinePullback.rationalPullback p k g n).map_add _ _).trans
        ((congrArg₂ (fun a b => a + b) hx hy).trans
          ((CrystallinePullback.rationalPullback p k (g ≫ h) n).map_add x y).symm))

end

end OAI.NumberTheory.PadicHodge.PeriodInvariants.CrystallinePullbackCoherence
