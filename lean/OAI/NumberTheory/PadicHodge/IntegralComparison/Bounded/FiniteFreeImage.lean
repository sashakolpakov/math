import OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.ImageAcyclicity

/-! # Finite Free Image -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.FiniteFreeImage

noncomputable section

/-!
# IntegralComparison: finite free slice modules give acyclic direct images at each level
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site
open OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.SliceImage

universe u

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p]
  {J : Ideal (WittVector p k)} {δ : DividedPowers J} {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of (WittVector p k))) [IsSeparated f] (n : ℕ)
  (U : BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) f n) (σ : Type) [Fintype σ]

instance sliceHasFiniteBiproducts : HasFiniteBiproducts (BoundedCrystalline.SliceSheaves.SliceSheaf f n U) :=
  HasFiniteBiproducts.of_hasFiniteProducts

def copies : σ → BoundedCrystalline.SliceSheaves.SliceSheaf f n U :=
  fun _ => BoundedCrystalline.SliceSheaves.structureSheaf f n U

def freeSheaf : BoundedCrystalline.SliceSheaves.SliceSheaf f n U :=
  biproduct (copies p k f n U σ)

abbrev Cohomology (i : ℕ) := Abelian.Ext.{u + 2}
  (BoundedCrystalline.CrystallineCohomology.constantUnit f n) ((SliceImage.directImage f n U).obj (freeSheaf p k f n U σ)) i

def cohomologyEquiv (i : ℕ) : Cohomology p k f n U σ i ≃+
    (σ → ImageAcyclicity.Cohomology p k f n U i) :=
  Abelian.Ext.addEquivBiproduct (BoundedCrystalline.CrystallineCohomology.constantUnit f n)
    (isBilimitOfPreserves (SliceImage.directImage f n U) (biproduct.isBilimit (copies p k f n U σ))) i

theorem positive_cohomology_zero (i : ℕ) : Subsingleton (Cohomology p k f n U σ (i + 1)) := by
  have := ImageAcyclicity.positive_cohomology_zero p k f n U i
  exact (cohomologyEquiv p k f n U σ (i + 1)).toEquiv.subsingleton

def degreeZeroEquiv : Cohomology p k f n U σ 0 ≃+ (σ → ULift.{u + 1} U.obj.ring) :=
  (cohomologyEquiv p k f n U σ 0).trans
    (AddEquiv.piCongrRight (fun _ => ImageAcyclicity.degreeZeroEquiv p k f n U))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.FiniteFreeImage
