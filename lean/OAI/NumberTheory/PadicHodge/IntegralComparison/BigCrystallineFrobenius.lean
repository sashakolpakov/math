import OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineCohomology
import OAI.NumberTheory.PadicHodge.IntegralComparison.Global.FrobeniusGeometry
import OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline

/-! # Big Crystalline Frobenius -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineFrobenius

noncomputable section

/-!
# IntegralComparison: q-Frobenius on big crystalline cohomology

The actual global scheme Frobenius induces a Witt-linear cohomology
endomorphism via the proved exact restriction functor. Extending scalars
gives an endomorphism over Frac(W(k)). No trace, eigenvalue, finite-dimension,
or comparison assertion is used to construct this operator.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

open OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline OAI.AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers

variable (p : ℕ) [Fact p.Prime]
variable (k : Type u) [Field k] [CharP k p] [Fintype k]
variable (X : Over (Spec (CommRingCat.of k)))

local notation "W" => WittVector p k
local notation "K₀" => FractionRing (WittVector p k)

def schemeFrobenius (a : ℕ) : X.left ⟶ X.left :=
  Global.FrobeniusGeometry.qFrobenius p (Fact.out : p.Prime) k X.hom a

lemma schemeFrobenius_over_witt (a : ℕ) (hcard : Fintype.card k = p ^ a) :
    schemeFrobenius p k X a ≫ Witt.Crystalline.wittStructureMap p k X = Witt.Crystalline.wittStructureMap p k X := by
  change schemeFrobenius p k X a ≫
      (X.hom ≫ Spec.map (CommRingCat.ofHom (WittVector.constantCoeff : W →+* k))) = _
  rw [← Category.assoc]
  have h := Global.FrobeniusGeometry.qFrobenius_over p (Fact.out : p.Prime) k X.hom a hcard
  exact congrArg (fun t => t ≫ Spec.map (CommRingCat.ofHom (WittVector.constantCoeff : W →+* k))) h

abbrev IntegralCohomology (n : ℕ) :=
  BigCrystallineCohomology.Cohomology
    (p := p) (J := Ideal.span {(p : W)}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) (Witt.Crystalline.wittStructureMap p k X) n

def integralFrobenius (a : ℕ) (hcard : Fintype.card k = p ^ a) (n : ℕ) :
    IntegralCohomology p k X n →ₗ[W] IntegralCohomology p k X n := by
  let F := BigCrystallineCohomology.pullback
    (p := p) (J := Ideal.span {(p : W)}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k)
    (schemeFrobenius p k X a) (schemeFrobenius_over_witt p k X a hcard) n
  refine { F.toAddMonoidHom with map_smul' := ?_ }
  intro b x
  change F ((ULift.up b : ULift.{u + 1} W) • x) = (ULift.up b : ULift.{u + 1} W) • F x
  exact F.map_smul _ _

abbrev RationalCohomology (n : ℕ) := TensorProduct W K₀ (IntegralCohomology p k X n)

def rationalFrobenius (a : ℕ) (hcard : Fintype.card k = p ^ a) (n : ℕ) :
    RationalCohomology p k X n →ₗ[K₀] RationalCohomology p k X n :=
  (integralFrobenius p k X a hcard n).baseChange K₀

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineFrobenius
