import OAI.NumberTheory.PadicHodge.IntegralComparison.BalancedBounded.CechCup
import OAI.NumberTheory.PadicHodge.IntegralComparison.GradedCupUnit
import OAI.NumberTheory.PadicHodge.IntegralComparison.Cosimplicial.ModuleCupAlgebra

/-! # Cup Unit -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.BalancedBounded.CupUnit

noncomputable section

/-! The genuine coefficient-one class is a unit for the balanced cup
on the original bounded crystalline Ext groups. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site

universe u

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p]
  {J : Ideal (WittVector p k)} {δ : DividedPowers J} {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of (WittVector p k))) [IsSeparated f] (n : ℕ)
  {ι : Type u} (F : ι → BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) f n)
  (hcover : ∀ U, CoveringObjectsSheafDetection.sieve F U ∈ BoundedCrystalline.Site.topology f n U)

local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := WittVector p k)
local notation "H" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.CrystallineCohomology.Cohomology (p := p) (J := J) (δ := δ) f n
local notation "A" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.CechCup.cochainAlgebra f n F
local notation "e" => OAI.NumberTheory.PadicHodge.IntegralComparison.BalancedBounded.CechCup.cohomologyEquiv p k f n F hcover
local notation "μ" => OAI.NumberTheory.PadicHodge.IntegralComparison.BalancedBounded.CechCup.cup p k f n F hcover

def one : H 0 := e 0 (Cosimplicial.ModuleCupAlgebra.cohomologyOne A)

theorem one_cup (i : ℕ) (x : H i) :
    GradedCupTransport.degreeCast R H (Nat.zero_add i) (μ 0 i (one p k f n F hcover) x) = x :=
  GradedCupUnit.transported_left R (fun i => (Cosimplicial.ModuleComplex.complex A).homology i) H
    e (Cosimplicial.ModuleCup.cohomologyCup A) (Cosimplicial.ModuleCupAlgebra.cohomologyOne A)
    (fun _ x => Cosimplicial.ModuleCupAlgebra.cohomologyOne_cup A x) i x

theorem cup_one (i : ℕ) (x : H i) : μ i 0 x (one p k f n F hcover) = x :=
  GradedCupUnit.transported_right R (fun i => (Cosimplicial.ModuleComplex.complex A).homology i) H
    e (Cosimplicial.ModuleCup.cohomologyCup A) (Cosimplicial.ModuleCupAlgebra.cohomologyOne A)
    (fun _ x => Cosimplicial.ModuleCupAlgebra.cohomologyCup_one A x) i x

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.BalancedBounded.CupUnit
