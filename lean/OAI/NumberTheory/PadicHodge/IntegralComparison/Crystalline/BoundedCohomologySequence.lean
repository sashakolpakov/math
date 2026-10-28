import OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.BoundedProductCohomology
import OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ResolutionHomologySequence
import OAI.NumberTheory.PadicHodge.IntegralComparison.ShortComplexTransport

/-! # Bounded Cohomology Sequence -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.BoundedCohomologySequence

noncomputable section

/-!
# IntegralComparison: an exact sequence relating original crystalline Ext and bounded-level Ext
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction

universe u

variable {p : ℕ} {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
  {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of B))

local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := B)
local notation "S" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ResolutionComplexExact.sequence (p := p) (J := J) (δ := δ) f

def productIso (i : ℕ) :
    (ModuleCat.uliftFunctor.{u + 2, u + 1} R).obj ((S).X₂.homology i) ≅
      ModuleCat.of R (∀ n, BoundedCrystalline.CrystallineCohomology.Cohomology (p := p) (J := J) (δ := δ) f n i) :=
  (ULift.moduleEquiv.trans (BoundedProductCohomology.productHomologyLinearEquiv f i)).toModuleIso

def sourceIso (i : ℕ) :
    (ModuleCat.uliftFunctor.{u + 2, u + 1} R).obj ((S).X₁.homology i) ≅
      ModuleCat.of R (BigCrystallineCohomology.Cohomology (p := p) (J := J) (δ := δ) f i) :=
  ResolutionComplexExact.sourceHomologyIso f i

def before (i : ℕ) : ShortComplex (ModuleCat.{u + 2} R) :=
  ShortComplexTransport.sequence
    ((ResolutionHomologySequence.before (p := p) (J := J) (δ := δ) f i).map
      (ModuleCat.uliftFunctor.{u + 2, u + 1} R))
    (productIso f i) (sourceIso f (i + 1)) (productIso f (i + 1))

def middle (i : ℕ) : ShortComplex (ModuleCat.{u + 2} R) :=
  ShortComplexTransport.sequence
    ((ResolutionHomologySequence.middle (p := p) (J := J) (δ := δ) f i).map
      (ModuleCat.uliftFunctor.{u + 2, u + 1} R))
    (sourceIso f i) (productIso f i) (productIso f i)

def after (i : ℕ) : ShortComplex (ModuleCat.{u + 2} R) :=
  ShortComplexTransport.sequence
    ((ResolutionHomologySequence.after (p := p) (J := J) (δ := δ) f i).map
      (ModuleCat.uliftFunctor.{u + 2, u + 1} R))
    (productIso f i) (productIso f i) (sourceIso f (i + 1))

theorem before_exact (i : ℕ) : (before (p := p) (J := J) (δ := δ) f i).Exact :=
  ShortComplexTransport.exact _ _ _ _
    ((ResolutionHomologySequence.before_exact f i).map (ModuleCat.uliftFunctor.{u + 2, u + 1} R))

theorem middle_exact (i : ℕ) : (middle (p := p) (J := J) (δ := δ) f i).Exact :=
  ShortComplexTransport.exact _ _ _ _
    ((ResolutionHomologySequence.middle_exact f i).map (ModuleCat.uliftFunctor.{u + 2, u + 1} R))

theorem after_exact (i : ℕ) : (after (p := p) (J := J) (δ := δ) f i).Exact :=
  ShortComplexTransport.exact _ _ _ _
    ((ResolutionHomologySequence.after_exact f i).map (ModuleCat.uliftFunctor.{u + 2, u + 1} R))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.BoundedCohomologySequence
