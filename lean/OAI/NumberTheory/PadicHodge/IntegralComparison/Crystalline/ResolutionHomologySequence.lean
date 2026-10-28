import OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ResolutionComplexExact
import Mathlib.Algebra.Homology.HomologySequence

/-! # Resolution Homology Sequence -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ResolutionHomologySequence

noncomputable section

/-!
# IntegralComparison: the long exact cohomology sequence of the actual inverse-limit resolution
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction

universe u

variable {p : ℕ} {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
  {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of B))

local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := B)
local notation "S" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ResolutionComplexExact.sequence (p := p) (J := J) (δ := δ) f
local notation "hS" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ResolutionComplexExact.shortExact (p := p) (J := J) (δ := δ) f

def before (i : ℕ) : ShortComplex (ModuleCat.{u + 1} R) :=
  ShortComplex.mk ((hS).δ i (i + 1) rfl) (HomologicalComplex.homologyMap (S).f (i + 1))
    ((hS).δ_comp i (i + 1) rfl)

def middle (i : ℕ) : ShortComplex (ModuleCat.{u + 1} R) :=
  (S).map (HomologicalComplex.homologyFunctor _ _ i)

def after (i : ℕ) : ShortComplex (ModuleCat.{u + 1} R) :=
  ShortComplex.mk (HomologicalComplex.homologyMap (S).g i) ((hS).δ i (i + 1) rfl)
    ((hS).comp_δ i (i + 1) rfl)

theorem before_exact (i : ℕ) : (before (p := p) (J := J) (δ := δ) f i).Exact :=
  (hS).homology_exact₁ i (i + 1) rfl

theorem middle_exact (i : ℕ) : (middle (p := p) (J := J) (δ := δ) f i).Exact :=
  (hS).homology_exact₂ i

theorem after_exact (i : ℕ) : (after (p := p) (J := J) (δ := δ) f i).Exact :=
  (hS).homology_exact₃ i (i + 1) rfl

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ResolutionHomologySequence
