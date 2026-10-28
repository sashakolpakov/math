import OAI.AlgebraicGeometry.Crystalline.Cohomology.WittPolynomial.EnvelopeFrobenius
import OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.DeRhamSemilinearMap
import OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.PDDeRham

/-! # Frame Frobenius -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.WittPolynomial.FrameFrobenius.WittPolynomialFrameFrobenius

noncomputable section

/-! # The actual Frobenius lift on every polynomial crystalline frame -/

universe u

variable (p : ℕ) [Fact p.Prime] (k σ : Type u) [Field k] [CharP k p] [PerfectRing k p]

local notation "W" => WittVector p k
local notation "P" => MvPolynomial σ W
local notation "B" => MvPolynomial σ k
local notation "I" => Ideal.span {(p : W)}
local notation "δ₀" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k
local notation "r" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Polynomial.AbsoluteFrobenius.PolynomialAbsoluteFrobenius.reduction p k σ
local notation "hr" => OAI.AlgebraicGeometry.Crystalline.Cohomology.WittPolynomial.Residue.WittPolynomialResidue.reduction_surjective p k σ
local notation "hb" => OAI.AlgebraicGeometry.Crystalline.Cohomology.WittPolynomial.Residue.WittPolynomialResidue.reduction_base p k σ
local notation "E" => OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.EnvelopeDp.PDEnvelope.Envelope W P I δ₀ (RingHom.ker r)
local notation "rE" => OAI.AlgebraicGeometry.Crystalline.Cohomology.EnvelopeThickeningP.EnvelopeThickening.envelopeReduction p k B P r hr hb
local notation "δE" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Affine.EnvelopeFrames.AffineEnvelopeFrames.envelopeDP p k B P r hr hb
local notation "hδE" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Affine.EnvelopeFrames.AffineEnvelopeFrames.envelope_baseDP p k B P r hr hb
local notation "F" => OAI.AlgebraicGeometry.Crystalline.Cohomology.WittPolynomial.EnvelopeFrobenius.WittPolynomialEnvelopeFrobenius.map p k σ
local notation "φ" => WittVector.frobeniusEquiv p k
local notation "T" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Affine.EnvelopeFrames.AffineEnvelopeFrames.frame p k B P r hr hb
local notation "Tower" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Affine.EnvelopeFrames.AffineEnvelopeFrames.tower p k B P r hr hb

local instance envelopeBaseAlgebra : Algebra W E :=
  ((PD.EnvelopeDp.PDEnvelope.ofAlgebra W P I δ₀ (RingHom.ker r)).comp (algebraMap W P)).toAlgebra

def levelMap (n : ℕ) : (T n).ring →+* (T n).ring :=
  Ideal.quotientMap (PadicPDP.PadicPDThickening.ideal p E n) F (by
    rw [← Ideal.map_le_iff_le_comap]
    simp only [PadicPDP.PadicPDThickening.ideal, Ideal.map_pow, Ideal.map_span, Set.image_singleton, map_natCast]
    exact le_rfl)

theorem levelMap_mk (n : ℕ) (x : E) :
    levelMap p k σ n (Ideal.Quotient.mk (PadicPDP.PadicPDThickening.ideal p E n) x) =
      Ideal.Quotient.mk (PadicPDP.PadicPDThickening.ideal p E n) (F x) := rfl

theorem levelMap_base (n : ℕ) (w : W) :
    levelMap p k σ n (algebraMap W (T n).ring w) = algebraMap W (T n).ring ((φ).toRingHom w) := by
  change Ideal.Quotient.mk (PadicPDP.PadicPDThickening.ideal p E n) (F (algebraMap W E w)) =
    Ideal.Quotient.mk (PadicPDP.PadicPDThickening.ideal p E n) (algebraMap W E ((φ).toRingHom w))
  rw [EnvelopeFrobenius.WittPolynomialEnvelopeFrobenius.map_base]

theorem levelMap_reduction (n : ℕ) (x : (T n).ring) :
    (T n).reduction (levelMap p k σ n x) = frobenius B p ((T n).reduction x) := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  exact EnvelopeFrobenius.WittPolynomialEnvelopeFrobenius.reduction_map p k σ x

theorem levelMap_isDPMorphism (n : ℕ) :
    DividedPowers.IsDPMorphism (T n).dividedPowers (T n).dividedPowers (levelMap p k σ n) := by
  apply DividedPowers.IsDPMorphism.of_comp δE (T n).dividedPowers (T n).dividedPowers
    (Ideal.Quotient.mk (PadicPDP.PadicPDThickening.ideal p E n)) (levelMap p k σ n)
    (PadicPDP.PadicPDThickening.reduction_kernel p k B E rE δE hδE n)
    (PadicPDP.PadicPDThickening.quotient_isDPMorphism p k B E rE δE hδE n)
  exact (PadicPDP.PadicPDThickening.quotient_isDPMorphism p k B E rE δE hδE n).comp _
    (EnvelopeFrobenius.WittPolynomialEnvelopeFrobenius.map_isDPMorphism p k σ)

theorem levelMap_transition (n m : ℕ) (h : n ≤ m) (x : (T m).ring) :
    levelMap p k σ n ((PD.InverseLimit.PDInverseLimit.transition p k B Tower n m h).hom x) =
      (PD.InverseLimit.PDInverseLimit.transition p k B Tower n m h).hom (levelMap p k σ m x) := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  rfl

def formsMap (m n : ℕ) : PD.PDDeRham.Form p k B Tower n m →ₛₗ[(φ).toRingHom]
    PD.PDDeRham.Form p k B Tower n m :=
  PD.DeRhamSemilinearMap.PDDeRhamSemilinearMap.formMap W W (T m).ring (T m).ring (φ).toRingHom
    (levelMap p k σ m) (levelMap_base p k σ m)
    (RingHom.ker (T m).reduction) (T m).dividedPowers
    (RingHom.ker (T m).reduction) (T m).dividedPowers (levelMap_isDPMorphism p k σ m) n

theorem formsMap_symbol (m n : ℕ) (a : (T m).ring) (v : Fin n → (T m).ring) :
    formsMap p k σ m n (PD.DeRham.PDDeRham.symbol W (T m).ring (RingHom.ker (T m).reduction)
      (T m).dividedPowers a v) =
        PD.DeRham.PDDeRham.symbol W (T m).ring (RingHom.ker (T m).reduction) (T m).dividedPowers
          (levelMap p k σ m a) (levelMap p k σ m ∘ v) :=
  PD.DeRhamSemilinearMap.PDDeRhamSemilinearMap.formMap_symbol W W (T m).ring (T m).ring (φ).toRingHom
    (levelMap p k σ m) (levelMap_base p k σ m)
    (RingHom.ker (T m).reduction) (T m).dividedPowers
    (RingHom.ker (T m).reduction) (T m).dividedPowers (levelMap_isDPMorphism p k σ m) n a v

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.WittPolynomial.FrameFrobenius.WittPolynomialFrameFrobenius
