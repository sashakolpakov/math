import OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.Site
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers

/-! # Crystalline -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline

noncomputable section

/-!
# IntegralComparison: the actual Witt-vector crystalline base and rational cohomology

The divided powers on (p) are imported from a proved arithmetic helper,
not from an Cohomology statement or comparison theorem. The site consists of
affine divided-power thickenings of opens of X over this Witt-vector base.
Rational coefficients are obtained by tensoring with Frac(W(k)).
No finiteness, cohomological Frobenius, or trace comparison is assumed.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

open OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.Site
open OAI.AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers

variable (p : ℕ) [Fact p.Prime]
variable (k : Type u) [Field k] [CharP k p] [PerfectRing k p]

local notation "W" => WittVector p k
local notation "K₀" => FractionRing (WittVector p k)

/-- The special fiber regarded as a scheme over the Witt-vector ring. -/
def wittStructureMap (X : Over (Spec (CommRingCat.of k))) :
    X.left ⟶ Spec (CommRingCat.of W) :=
  X.hom ≫ Spec.map (CommRingCat.ofHom (WittVector.constantCoeff : W →+* k))

/-- The affine crystalline site of the given special fiber over W(k). -/
abbrev CrystallineObject (X : Over (Spec (CommRingCat.of k))) :=
  Crystalline.Site.AffineThickening p W (Ideal.span {(p : W)}) (AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k)
    (wittStructureMap p k X)

/-- Integral crystalline cohomology with the actual Witt-vector action. -/
abbrev integralCohomology (X : Over (Spec (CommRingCat.of k))) (n : ℕ) : Type (u + 2) :=
  Crystalline.Site.AffineThickening.IntegralModuleCohomology
    (p := p) (B := W) (J := Ideal.span {(p : W)}) (δB := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k)
    (f := wittStructureMap p k X) n

/-- Rational crystalline cohomology, defined by scalar extension from
the integral geometric cohomology group. -/
def rationalCohomology (X : Over (Spec (CommRingCat.of k))) (n : ℕ) : ModuleCat.{u + 2} K₀ :=
  ModuleCat.of K₀ (TensorProduct W K₀ (integralCohomology p k X n))

/-- The canonical Witt Frobenius is a morphism of divided-power rings. -/
def wittFrobeniusDP :
    DividedPowers.DPMorphism (AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) (AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) where
  toRingHom := (WittVector.frobeniusEquiv p k).toRingHom
  ideal_comp := Ideal.map_le_iff_le_comap.mpr (fun x hx => AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.frobenius_mem p k x hx)
  dpow_comp x hx := (AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.frobenius_dpow p k _ x hx).symm

@[simp]
lemma wittFrobeniusDP_apply (x : W) : wittFrobeniusDP p k x = WittVector.frobenius x := rfl

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline
