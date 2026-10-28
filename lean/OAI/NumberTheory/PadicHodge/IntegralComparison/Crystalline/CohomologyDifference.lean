import OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.BoundedCohomologySequence
import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedSection.CohomologyDifference
import OAI.NumberTheory.PadicHodge.IntegralComparison.ProductLinearDifference

/-! # Cohomology Difference -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.CohomologyDifference

noncomputable section

/-!
# IntegralComparison: the inverse-system difference on the original bounded crystalline Ext groups

The transition maps are induced by restriction of the original injective
resolution, then transported through its bounded-level Ext comparison.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site

universe u

variable {p : ℕ} {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
  {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of B))

local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := B)
local notation "P" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site.property (p := p) (J := J) (δ := δ) f
local notation "A" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ResolutionComplexExact.presheafComplex (p := p) (J := J) (δ := δ) f
local notation "F" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.BoundedProductCohomology.family (p := p) (J := J) (δ := δ) f
local notation "d" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedSection.ComplexExact.difference R P
  (BoundedSection.Reconstruction.monotone_property f) (ModuleCat.of R R) A

def componentTransition (n m : ℕ) (hnm : n ≤ m) :
    BoundedProductCohomology.component (p := p) (J := J) (δ := δ) f m ⟶
      BoundedProductCohomology.component (p := p) (J := J) (δ := δ) f n :=
  BoundedSection.FamilyDifference.Family.transition R P (BoundedSection.Reconstruction.monotone_property f)
    (ModuleCat.of R R) A n m hnm

def transition (n i : ℕ) :
    BoundedCrystalline.CrystallineCohomology.Cohomology (p := p) (J := J) (δ := δ) f (n + 1) i →ₗ[R]
      BoundedCrystalline.CrystallineCohomology.Cohomology (p := p) (J := J) (δ := δ) f n i :=
  (BoundedProductCohomology.componentLinearEquiv f n i).toLinearMap.comp
    ((HomologicalComplex.homologyMap (componentTransition f n (n + 1) (Nat.le_succ n)) i).hom.comp
      (BoundedProductCohomology.componentLinearEquiv f (n + 1) i).symm.toLinearMap)

def difference (i : ℕ) :
    (∀ n, BoundedCrystalline.CrystallineCohomology.Cohomology (p := p) (J := J) (δ := δ) f n i) →ₗ[R]
      ∀ n, BoundedCrystalline.CrystallineCohomology.Cohomology (p := p) (J := J) (δ := δ) f n i :=
  SequentialModuleDifference.difference R _ (fun n => transition f n i)

def sequenceDifference (i : ℕ) :
    (∀ n, BoundedCrystalline.CrystallineCohomology.Cohomology (p := p) (J := J) (δ := δ) f n i) →ₗ[R]
      ∀ n, BoundedCrystalline.CrystallineCohomology.Cohomology (p := p) (J := J) (δ := δ) f n i :=
  (BoundedCohomologySequence.middle (p := p) (J := J) (δ := δ) f i).g.hom

theorem middle_g_apply (i : ℕ)
    (x : ∀ n, BoundedCrystalline.CrystallineCohomology.Cohomology (p := p) (J := J) (δ := δ) f n i) (n : ℕ) :
    sequenceDifference (p := p) (J := J) (δ := δ) f i x n =
      x n - transition f n i (x (n + 1)) := by
  change ProductLinearDifference.transport R
    (fun n => (BoundedProductCohomology.component f n).homology i)
    (fun n => BoundedCrystalline.CrystallineCohomology.Cohomology f n i)
    (fun n => BoundedProductCohomology.componentLinearEquiv f n i)
    (CountableCohomologyDifference.difference R F d i).hom x n = _
  exact ProductLinearDifference.transport_apply R _ _
    (fun n => BoundedProductCohomology.componentLinearEquiv f n i)
    (fun n => (HomologicalComplex.homologyMap (componentTransition f n (n + 1) (Nat.le_succ n)) i).hom)
    _ (BoundedSection.CohomologyDifference.difference_apply R P
      (BoundedSection.Reconstruction.monotone_property f) (ModuleCat.of R R) A i) x n

theorem middle_g_eq (i : ℕ) :
    sequenceDifference (p := p) (J := J) (δ := δ) f i = difference (p := p) (J := J) (δ := δ) f i := by
  apply LinearMap.ext
  intro x
  exact funext (middle_g_apply (p := p) (J := J) (δ := δ) f i x)

def compatible (i : ℕ) :
    Submodule R (∀ n, BoundedCrystalline.CrystallineCohomology.Cohomology (p := p) (J := J) (δ := δ) f n i) :=
  LinearMap.ker (difference (p := p) (J := J) (δ := δ) f i)

theorem mem_compatible (i : ℕ)
    (x : ∀ n, BoundedCrystalline.CrystallineCohomology.Cohomology (p := p) (J := J) (δ := δ) f n i) :
    x ∈ compatible (p := p) (J := J) (δ := δ) f i ↔
      ∀ n, transition (p := p) (J := J) (δ := δ) f n i (x (n + 1)) = x n :=
  SequentialModuleDifference.difference_eq_zero_iff R
    (fun n => BoundedCrystalline.CrystallineCohomology.Cohomology (p := p) (J := J) (δ := δ) f n i)
    (fun n => transition (p := p) (J := J) (δ := δ) f n i) x

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.CohomologyDifference
