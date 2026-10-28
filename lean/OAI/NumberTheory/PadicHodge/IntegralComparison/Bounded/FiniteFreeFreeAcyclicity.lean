import OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.FiniteFreeImage
import OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.ImageFreeAcyclicity

/-! # Finite Free Free Acyclicity -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.FiniteFreeFreeAcyclicity

noncomputable section

/-! Finite free slice direct images are acyclic for every native free representable source. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site
open OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.SliceImage

universe u

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p]
  {J : Ideal (WittVector p k)} {δ : DividedPowers J} {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of (WittVector p k))) [IsSeparated f] (n : ℕ)
  (U V : BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) f n) (σ : Type) [Fintype σ]

local notation "CR" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := WittVector p k)
local notation "source" => Sheaf.freeYoneda (OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site.topology f n) V (ModuleCat.of CR CR)

abbrev Cohomology (i : ℕ) := Abelian.Ext.{u + 2} source
  ((SliceImage.directImage f n U).obj (FiniteFreeImage.freeSheaf p k f n U σ)) i

def cohomologyEquiv (i : ℕ) : Cohomology p k f n U V σ i ≃+
    (σ → ImageFreeAcyclicity.Cohomology p k f n U V i) :=
  Abelian.Ext.addEquivBiproduct source
    (isBilimitOfPreserves (SliceImage.directImage f n U)
      (biproduct.isBilimit (FiniteFreeImage.copies p k f n U σ))) i

theorem positive_cohomology_zero (i : ℕ) : Subsingleton (Cohomology p k f n U V σ (i + 1)) := by
  have := ImageFreeAcyclicity.positive_cohomology_zero p k f n U V i
  exact (cohomologyEquiv p k f n U V σ (i + 1)).toEquiv.subsingleton

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.FiniteFreeFreeAcyclicity
