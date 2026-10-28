import OAI.NumberTheory.PadicHodge.PeriodInvariants.CrystallineSheafCoherence
import OAI.NumberTheory.PadicHodge.GeometricComparison.Crystalline.CoefficientAdapter
import OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.SheafInjectives

/-! # Crystalline Functoriality -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.CrystallineFunctoriality.CM

noncomputable section

/-! Identity and composition for GeometricComparison's actual big crystalline H1.
The proof uses exact restriction and its checked Ext transport directly. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped TensorProduct
universe u

namespace Big

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineCohomology
  NumberTheory.PadicHodge.PeriodInvariants.CrystallineRestrictionCoherence NumberTheory.PadicHodge.PeriodInvariants.CrystallineSheafCoherence NumberTheory.PadicHodge.PeriodInvariants.ExtTransport

variable {p : ℕ} {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
variable {X Y Z : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of B)}
  {fY : Y ⟶ Spec (CommRingCat.of B)} {fZ : Z ⟶ Spec (CommRingCat.of B)}

theorem pullback_id (n : ℕ) (x : NumberTheory.PadicHodge.IntegralComparison.BigCrystallineCohomology.Cohomology (p := p) (J := J) (δ := δ) f n) :
    NumberTheory.PadicHodge.IntegralComparison.BigCrystallineCohomology.pullback (𝟙 X) (Category.id_comp f) n x = x := by
  change NumberTheory.PadicHodge.PeriodInvariants.ExtTransport.exactTransport (NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := B)) (NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.restriction (𝟙 X) (Category.id_comp f))
    (NumberTheory.PadicHodge.IntegralComparison.BigCrystallineCohomology.constantTransport (𝟙 X) (Category.id_comp f)) (NumberTheory.PadicHodge.IntegralComparison.BigCrystallineCohomology.structureTransport (𝟙 X) (Category.id_comp f)) n x = x
  rw [NumberTheory.PadicHodge.PeriodInvariants.CrystallineSheafCoherence.constantTransport_id, NumberTheory.PadicHodge.PeriodInvariants.CrystallineSheafCoherence.structureTransport_id]
  have hn := NumberTheory.PadicHodge.PeriodInvariants.ExtTransport.exactTransport_natIso (NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := B)) NumberTheory.PadicHodge.PeriodInvariants.CrystallineRestrictionCoherence.restrictionId
    (Iso.refl (NumberTheory.PadicHodge.IntegralComparison.BigCrystallineCohomology.constantUnit f)) (Iso.refl (NumberTheory.PadicHodge.IntegralComparison.BigCrystallineCohomology.structureSheaf f)) x
  have ht := congrArg₂ (fun iA iB => NumberTheory.PadicHodge.PeriodInvariants.ExtTransport.exactTransport (NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := B))
    (NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.restriction (𝟙 X) (Category.id_comp f)) iA iB n x)
    (Iso.trans_refl (NumberTheory.PadicHodge.PeriodInvariants.CrystallineRestrictionCoherence.restrictionId.app (NumberTheory.PadicHodge.IntegralComparison.BigCrystallineCohomology.constantUnit f))).symm
    (Iso.trans_refl (NumberTheory.PadicHodge.PeriodInvariants.CrystallineRestrictionCoherence.restrictionId.app (NumberTheory.PadicHodge.IntegralComparison.BigCrystallineCohomology.structureSheaf f))).symm
  exact ht.trans (hn.trans (NumberTheory.PadicHodge.PeriodInvariants.ExtTransport.exactTransport_id (NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := B)) x))

theorem pullback_comp (g : X ⟶ Y) (hg : g ≫ fY = f) (h : Y ⟶ Z) (hh : h ≫ fZ = fY)
    (n : ℕ) (x : NumberTheory.PadicHodge.IntegralComparison.BigCrystallineCohomology.Cohomology (p := p) (J := J) (δ := δ) fZ n) :
    NumberTheory.PadicHodge.IntegralComparison.BigCrystallineCohomology.pullback g hg n (NumberTheory.PadicHodge.IntegralComparison.BigCrystallineCohomology.pullback h hh n x) = NumberTheory.PadicHodge.IntegralComparison.BigCrystallineCohomology.pullback (g ≫ h) (NumberTheory.PadicHodge.PeriodInvariants.CrystallineRestrictionCoherence.composite_over g hg h hh) n x := by
  change NumberTheory.PadicHodge.PeriodInvariants.ExtTransport.exactTransport (NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := B)) (NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.restriction g hg) (NumberTheory.PadicHodge.IntegralComparison.BigCrystallineCohomology.constantTransport g hg)
    (NumberTheory.PadicHodge.IntegralComparison.BigCrystallineCohomology.structureTransport g hg) n
    (NumberTheory.PadicHodge.PeriodInvariants.ExtTransport.exactTransport (NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := B)) (NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.restriction h hh) (NumberTheory.PadicHodge.IntegralComparison.BigCrystallineCohomology.constantTransport h hh)
      (NumberTheory.PadicHodge.IntegralComparison.BigCrystallineCohomology.structureTransport h hh) n x) =
    NumberTheory.PadicHodge.PeriodInvariants.ExtTransport.exactTransport (NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := B)) (NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.restriction (g ≫ h) (NumberTheory.PadicHodge.PeriodInvariants.CrystallineRestrictionCoherence.composite_over g hg h hh))
      (NumberTheory.PadicHodge.IntegralComparison.BigCrystallineCohomology.constantTransport (g ≫ h) (NumberTheory.PadicHodge.PeriodInvariants.CrystallineRestrictionCoherence.composite_over g hg h hh))
      (NumberTheory.PadicHodge.IntegralComparison.BigCrystallineCohomology.structureTransport (g ≫ h) (NumberTheory.PadicHodge.PeriodInvariants.CrystallineRestrictionCoherence.composite_over g hg h hh)) n x
  rw [NumberTheory.PadicHodge.PeriodInvariants.ExtTransport.exactTransport_comp, NumberTheory.PadicHodge.PeriodInvariants.CrystallineSheafCoherence.constantTransport_comp, NumberTheory.PadicHodge.PeriodInvariants.CrystallineSheafCoherence.structureTransport_comp]
  exact NumberTheory.PadicHodge.PeriodInvariants.ExtTransport.exactTransport_natIso (NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := B)) (NumberTheory.PadicHodge.PeriodInvariants.CrystallineRestrictionCoherence.restrictionComp g hg h hh)
    (NumberTheory.PadicHodge.IntegralComparison.BigCrystallineCohomology.constantTransport (g ≫ h) (NumberTheory.PadicHodge.PeriodInvariants.CrystallineRestrictionCoherence.composite_over g hg h hh))
    (NumberTheory.PadicHodge.IntegralComparison.BigCrystallineCohomology.structureTransport (g ≫ h) (NumberTheory.PadicHodge.PeriodInvariants.CrystallineRestrictionCoherence.composite_over g hg h hh)) x

end Big

open OAI.NumberTheory.PadicHodge.GeometricComparison.Crystalline.CoefficientAdapter

variable (q : ℕ) [Fact q.Prime]
  {X Y Z : Over (Spec (.of (ZMod q)))}

theorem rationalPullback_id (X : Over (Spec (.of (ZMod q)))) :
    NumberTheory.PadicHodge.GeometricComparison.Crystalline.CoefficientAdapter.rationalPullback q (𝟙 X) = LinearMap.id := by
  apply LinearMap.ext
  intro x
  induction x using TensorProduct.inductionOn with
  | tmul r x => exact congrArg (fun z => r ⊗ₜ[NumberTheory.PadicHodge.GeometricComparison.Crystalline.CoefficientAdapter.Witt q] z) (Big.pullback_id 1 x)
  | add x y hx hy => simp only [map_add, hx, hy, LinearMap.id_apply]

theorem rationalPullback_comp (f : X ⟶ Y) (g : Y ⟶ Z) :
    (NumberTheory.PadicHodge.GeometricComparison.Crystalline.CoefficientAdapter.rationalPullback q f).comp (NumberTheory.PadicHodge.GeometricComparison.Crystalline.CoefficientAdapter.rationalPullback q g) = NumberTheory.PadicHodge.GeometricComparison.Crystalline.CoefficientAdapter.rationalPullback q (f ≫ g) := by
  apply LinearMap.ext
  intro x
  change NumberTheory.PadicHodge.GeometricComparison.Crystalline.CoefficientAdapter.rationalPullback q f (NumberTheory.PadicHodge.GeometricComparison.Crystalline.CoefficientAdapter.rationalPullback q g x) = NumberTheory.PadicHodge.GeometricComparison.Crystalline.CoefficientAdapter.rationalPullback q (f ≫ g) x
  induction x using TensorProduct.inductionOn with
  | tmul r x =>
    exact congrArg (fun z => r ⊗ₜ[NumberTheory.PadicHodge.GeometricComparison.Crystalline.CoefficientAdapter.Witt q] z)
      (Big.pullback_comp f.left (by simp only [NumberTheory.PadicHodge.GeometricComparison.Crystalline.CoefficientAdapter.wittStructure, ← Category.assoc, Over.w])
        g.left (by simp only [NumberTheory.PadicHodge.GeometricComparison.Crystalline.CoefficientAdapter.wittStructure, ← Category.assoc, Over.w]) 1 x)
  | add x y hx hy => simp only [map_add, hx, hy]

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.CrystallineFunctoriality.CM
