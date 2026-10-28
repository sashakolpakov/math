import OAI.AlgebraicGeometry.Crystalline.Cohomology.FramedPolynomial.TowerDiagram
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Polynomial.EnvelopeForms
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Base.IdealQuotient

/-! # Polynomial Frame Derivatives -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.Affine.PolynomialFrameDerivatives.AffinePolynomialFrameDerivatives

noncomputable section

/-!
# Coordinate derivatives on the original affine p-power envelope levels

The actual envelope partial derivatives preserve each p-power ideal by
Witt-linearity. They therefore descend to the original frame rings,
commute there, and differentiate their fixed polynomial coordinates.
-/

universe u

variable (p : ℕ) [Fact p.Prime] (k B σ : Type u) [Field k] [CharP k p]
  [CommRing B] [Algebra k B]
  (r : MvPolynomial σ (WittVector p k) →+* B) (hr : Function.Surjective r)
  (hbase : r.comp (algebraMap (WittVector p k) (MvPolynomial σ (WittVector p k))) =
    (algebraMap k B).comp WittVector.constantCoeff)

local notation "W" => WittVector p k
local notation "A" => MvPolynomial σ W
local notation "I₀" => Ideal.span {(p : W)}
local notation "δ₀" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k
local notation "E" => OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.EnvelopeDp.PDEnvelope.Envelope W A I₀ δ₀ (RingHom.ker r)
local notation "T" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Affine.EnvelopeFrames.AffineEnvelopeFrames.frame p k B A r hr hbase

local instance envelopeBaseAlgebra : Algebra W E :=
  ((PD.EnvelopeDp.PDEnvelope.ofAlgebra W A I₀ δ₀ (RingHom.ker r)).comp (algebraMap W A)).toAlgebra

def source (i : σ) : Derivation W E E :=
  Polynomial.EnvelopeForms.PolynomialEnvelopeForms.pderiv W σ I₀ δ₀ (RingHom.ker r)
    (EnvelopeThickeningP.EnvelopeThickening.baseIdeal_le_kernel p k B A r hbase) i

def quotient (n : ℕ) : E →ₐ[W] (T n).ring :=
  Ideal.Quotient.mkₐ W (PadicPDP.PadicPDThickening.ideal p E n)

theorem stable (n : ℕ) (i : σ) (x : E) (hx : quotient p k B σ r hr hbase n x = 0) :
    quotient p k B σ r hr hbase n (source p k B σ r hbase i x) = 0 := by
  let L : Ideal W := I₀ ^ (n + 1)
  have he : L.map (algebraMap W E) = PadicPDP.PadicPDThickening.ideal p E n := by
    simp only [L, Ideal.map_pow, Ideal.map_span, Set.image_singleton, map_natCast, PadicPDP.PadicPDThickening.ideal]
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  rw [← he]
  apply Base.IdealQuotient.BaseIdealQuotient.map_mem L (source p k B σ r hbase i).toLinearMap
  rw [he]
  exact Ideal.Quotient.eq_zero_iff_mem.mp hx

def derivation (n : ℕ) (i : σ) : Derivation W (T n).ring (T n).ring :=
  Derivation.liftOfSurjective (f := quotient p k B σ r hr hbase n)
    Ideal.Quotient.mk_surjective (stable p k B σ r hr hbase n i)

theorem derivation_quotient (n : ℕ) (i : σ) (x : E) :
    derivation p k B σ r hr hbase n i (quotient p k B σ r hr hbase n x) =
      quotient p k B σ r hr hbase n (source p k B σ r hbase i x) :=
  Derivation.liftOfSurjective_apply (M := (T n).ring) (f := quotient p k B σ r hr hbase n)
    Ideal.Quotient.mk_surjective (stable p k B σ r hr hbase n i) x

theorem coordinate (n : ℕ) (i j : σ) [Decidable (j = i)] :
    derivation p k B σ r hr hbase n i
      (EnvelopeFrameUniversal.AffineEnvelopeFrameUniversal.coefficient p k B A r hr hbase n (MvPolynomial.X j)) =
        if j = i then 1 else 0 := by
  change derivation p k B σ r hr hbase n i (quotient p k B σ r hr hbase n
    (Polynomial.EnvelopeForms.PolynomialEnvelopeForms.coordinate W σ I₀ δ₀ (RingHom.ker r) j)) = _
  rw [derivation_quotient]
  change quotient p k B σ r hr hbase n
    (Polynomial.EnvelopeForms.PolynomialEnvelopeForms.pderiv W σ I₀ δ₀ (RingHom.ker r)
      (EnvelopeThickeningP.EnvelopeThickening.baseIdeal_le_kernel p k B A r hbase) i
        (Polynomial.EnvelopeForms.PolynomialEnvelopeForms.coordinate W σ I₀ δ₀ (RingHom.ker r) j)) = _
  rw [Polynomial.EnvelopeForms.PolynomialEnvelopeForms.pderiv_coordinate]
  split_ifs <;> simp only [map_one, map_zero]

theorem commute (n : ℕ) (i j : σ) : Function.Commute
    (derivation p k B σ r hr hbase n i) (derivation p k B σ r hr hbase n j) := by
  intro x
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  change derivation p k B σ r hr hbase n i
    (derivation p k B σ r hr hbase n j (quotient p k B σ r hr hbase n x)) =
      derivation p k B σ r hr hbase n j
        (derivation p k B σ r hr hbase n i (quotient p k B σ r hr hbase n x))
  rw [derivation_quotient, derivation_quotient, derivation_quotient, derivation_quotient]
  exact congrArg (quotient p k B σ r hr hbase n)
    (Polynomial.EnvelopeForms.PolynomialEnvelopeForms.pderiv_commute W σ I₀ δ₀ (RingHom.ker r)
      (EnvelopeThickeningP.EnvelopeThickening.baseIdeal_le_kernel p k B A r hbase) i j x)

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.Affine.PolynomialFrameDerivatives.AffinePolynomialFrameDerivatives
