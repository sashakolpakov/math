import OAI.NumberTheory.PadicHodge.IntegralComparison.Balanced.SmoothProperWittCup
import OAI.NumberTheory.PadicHodge.IntegralComparison.Cosimplicial.Anticommutativity
import OAI.NumberTheory.PadicHodge.IntegralComparison.GradedCupTransport

/-! # Cup Algebra -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.BalancedBounded.CupAlgebra

noncomputable section

/-! The balanced cup on the original bounded Ext groups is associative,
and its degree-one products anticommute over the integral coefficient ring. -/

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
local notation "μ" => OAI.NumberTheory.PadicHodge.IntegralComparison.BalancedBounded.CechCup.cup p k f n F hcover

theorem assoc (i j l : ℕ) (x : H i) (y : H j) (z : H l) :
    GradedCupTransport.degreeCast R H (Nat.add_assoc i j l)
      (μ (i + j) l (μ i j x y) z) = μ i (j + l) x (μ j l y z) :=
  GradedCupTransport.assoc R (fun i => (Cosimplicial.ModuleComplex.complex A).homology i) H
    (CechCup.cohomologyEquiv p k f n F hcover)
    (Cosimplicial.ModuleCup.cohomologyCup A)
    (fun _ _ _ x y z => Cosimplicial.ModuleCupAlgebra.cohomologyCup_assoc A x y z) i j l x y z

theorem one_add_swap (x y : H 1) : μ 1 1 x y + μ 1 1 y x = 0 :=
  GradedCupTransport.one_add_swap R (fun i => (Cosimplicial.ModuleComplex.complex A).homology i) H
    (CechCup.cohomologyEquiv p k f n F hcover)
    (Cosimplicial.ModuleCup.cohomologyCup A)
    (Cosimplicial.Anticommutativity.ModuleCup.cup_one_add_swap A) x y

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.BalancedBounded.CupAlgebra
