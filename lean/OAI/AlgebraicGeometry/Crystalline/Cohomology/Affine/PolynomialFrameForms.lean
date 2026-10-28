import OAI.AlgebraicGeometry.Crystalline.Cohomology.Affine.PolynomialFramePD
import OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.CoordinateBasis
import OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.DeRhamTensor

/-! # Polynomial Frame Forms -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.Affine.PolynomialFrameForms.AffinePolynomialFrameForms

noncomputable section

/-!
# Coordinate forms on the original affine crystalline frame

The actual finite-level PD de Rham complex is the coordinate tensor
complex for the derivatives descended from the universal envelope.
The isomorphism includes every degree and the original differential.
-/

open _root_.CategoryTheory Classical

universe u

variable (p : ℕ) [Fact p.Prime] (k B σ : Type u) [Field k] [CharP k p]
  [CommRing B] [Algebra k B]
  (r : MvPolynomial σ (WittVector p k) →+* B) (hr : Function.Surjective r)
  (hbase : r.comp (algebraMap (WittVector p k) (MvPolynomial σ (WittVector p k))) =
    (algebraMap k B).comp WittVector.constantCoeff)

local notation "W" => WittVector p k
local notation "Poly" => MvPolynomial σ W
local notation "I₀" => Ideal.span {(p : W)}
local notation "δ₀" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k
local notation "E" => OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.EnvelopeDp.PDEnvelope.Envelope W Poly I₀ δ₀ (RingHom.ker r)
local notation "IE" => OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.EnvelopeDp.PDEnvelope.ideal W Poly I₀ δ₀ (RingHom.ker r)
local notation "δE" => OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.EnvelopeDp.PDEnvelope.dividedPowers W Poly I₀ δ₀ (RingHom.ker r)
local notation "rE" => OAI.AlgebraicGeometry.Crystalline.Cohomology.EnvelopeThickeningP.EnvelopeThickening.envelopeReduction p k B Poly r hr hbase
local notation "T" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Affine.EnvelopeFrames.AffineEnvelopeFrames.frame p k B Poly r hr hbase
local notation "q" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Affine.PolynomialFrameDerivatives.AffinePolynomialFrameDerivatives.quotient p k B σ r hr hbase
local notation "D" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Affine.PolynomialFrameDerivatives.AffinePolynomialFrameDerivatives.derivation p k B σ r hr hbase
local notation "x" => fun n i => OAI.AlgebraicGeometry.Crystalline.Cohomology.Affine.EnvelopeFrameUniversal.AffineEnvelopeFrameUniversal.coefficient p k B Poly r hr hbase n (MvPolynomial.X i)

local instance envelopeBaseAlgebra : Algebra W E :=
  ((PD.EnvelopeDp.PDEnvelope.ofAlgebra W Poly I₀ δ₀ (RingHom.ker r)).comp (algebraMap W Poly)).toAlgebra

theorem quotient_isDPMorphism (n : ℕ) :
    DividedPowers.IsDPMorphism δE (T n).dividedPowers (q n).toRingHom where
  ideal_comp := by
    rw [← EnvelopeThickeningP.EnvelopeThickening.envelopeReduction_kernel p k B Poly r hr hbase]
    exact (PolynomialFramePD.AffinePolynomialFramePD.quotient_isDPMorphism p k B σ r hr hbase n).ideal_comp
  dpow_comp a ha := by
    have ha' : a ∈ RingHom.ker rE :=
      (EnvelopeThickeningP.EnvelopeThickening.envelopeReduction_kernel p k B Poly r hr hbase).symm ▸ ha
    exact (PolynomialFramePD.AffinePolynomialFramePD.quotient_isDPMorphism p k B σ r hr hbase n).dpow_comp a ha'

def formMap (n j : ℕ) : PD.DeRham.PDDeRham.Form W E IE δE j →ₗ[W]
    PD.DeRham.PDDeRham.Form W (T n).ring (RingHom.ker (T n).reduction) (T n).dividedPowers j :=
  PD.DeRhamGlobal.PDDeRhamGlobal.formMap (CommAlgCat.ofHom (q n)) (quotient_isDPMorphism p k B σ r hr hbase n) j

theorem formMap_D (n : ℕ) (a : E) :
    formMap p k B σ r hr hbase n 1 (PD.OneForms.PDOneForms.D W E IE δE a) =
      PD.OneForms.PDOneForms.D W (T n).ring (RingHom.ker (T n).reduction) (T n).dividedPowers (q n a) :=
  PD.FormSurjective.PDFormSurjective.formMap_D (CommAlgCat.ofHom (q n)) (quotient_isDPMorphism p k B σ r hr hbase n) a

variable [Fintype σ]

theorem D_eq_sum (n : ℕ) (a : (T n).ring) :
    PD.OneForms.PDOneForms.D W (T n).ring (RingHom.ker (T n).reduction) (T n).dividedPowers a =
      ∑ i, D n i a • PD.OneForms.PDOneForms.D W (T n).ring (RingHom.ker (T n).reduction)
        (T n).dividedPowers (x n i) := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  change PD.OneForms.PDOneForms.D W (T n).ring (RingHom.ker (T n).reduction) (T n).dividedPowers (q n a) =
    ∑ i, D n i (q n a) • PD.OneForms.PDOneForms.D W (T n).ring (RingHom.ker (T n).reduction)
      (T n).dividedPowers (x n i)
  rw [← formMap_D, Polynomial.EnvelopeForms.PolynomialEnvelopeForms.D_eq_sum W σ I₀ δ₀ (RingHom.ker r)
    (EnvelopeThickeningP.EnvelopeThickening.baseIdeal_le_kernel p k B Poly r hbase), map_sum]
  apply Finset.sum_congr rfl
  intro i _
  have hs := PD.DeRhamGlobal.PDDeRhamGlobal.formMap_smul (CommAlgCat.ofHom (q n))
    (quotient_isDPMorphism p k B σ r hr hbase n) 1
    (PolynomialFrameDerivatives.AffinePolynomialFrameDerivatives.source p k B σ r hbase i a)
    (PD.OneForms.PDOneForms.D W E IE δE (Polynomial.EnvelopeForms.PolynomialEnvelopeForms.coordinate W σ I₀ δ₀ (RingHom.ker r) i))
  change formMap p k B σ r hr hbase n 1
    (PolynomialFrameDerivatives.AffinePolynomialFrameDerivatives.source p k B σ r hbase i a • _) =
      q n (PolynomialFrameDerivatives.AffinePolynomialFrameDerivatives.source p k B σ r hbase i a) •
        formMap p k B σ r hr hbase n 1 _ at hs
  change formMap p k B σ r hr hbase n 1
    (PolynomialFrameDerivatives.AffinePolynomialFrameDerivatives.source p k B σ r hbase i a •
      PD.OneForms.PDOneForms.D W E IE δE (Polynomial.EnvelopeForms.PolynomialEnvelopeForms.coordinate W σ I₀ δ₀ (RingHom.ker r) i)) = _
  rw [hs, formMap_D]
  change q n (PolynomialFrameDerivatives.AffinePolynomialFrameDerivatives.source p k B σ r hbase i a) •
    PD.OneForms.PDOneForms.D W (T n).ring (RingHom.ker (T n).reduction) (T n).dividedPowers (x n i) =
      D n i (q n a) • PD.OneForms.PDOneForms.D W (T n).ring (RingHom.ker (T n).reduction)
        (T n).dividedPowers (x n i)
  rw [PolynomialFrameDerivatives.AffinePolynomialFrameDerivatives.derivation_quotient]

def basis (n : ℕ) : Module.Basis σ (T n).ring
    (PD.DeRham.PDDeRham.Form W (T n).ring (RingHom.ker (T n).reduction) (T n).dividedPowers 1) :=
  PD.CoordinateBasis.PDCoordinateBasis.basis W (T n).ring σ (RingHom.ker (T n).reduction) (T n).dividedPowers
    (x n) (D n) (PolynomialFramePD.AffinePolynomialFramePD.dpow p k B σ r hr hbase n)
    (D_eq_sum p k B σ r hr hbase n)
    (fun i j => PolynomialFrameDerivatives.AffinePolynomialFrameDerivatives.coordinate p k B σ r hr hbase n i j)

theorem basis_apply (n : ℕ) (i : σ) : basis p k B σ r hr hbase n i =
    PD.OneForms.PDOneForms.D W (T n).ring (RingHom.ker (T n).reduction) (T n).dividedPowers (x n i) :=
  PD.CoordinateBasis.PDCoordinateBasis.basis_apply W (T n).ring σ (RingHom.ker (T n).reduction) (T n).dividedPowers
    (x n) (D n) (PolynomialFramePD.AffinePolynomialFramePD.dpow p k B σ r hr hbase n)
    (D_eq_sum p k B σ r hr hbase n)
    (fun i j => PolynomialFrameDerivatives.AffinePolynomialFrameDerivatives.coordinate p k B σ r hr hbase n i j) i

variable [LinearOrder σ]

def complexIso (n : ℕ) :
    Koszul.Tensor.KoszulTensor.complex W σ (T n).ring (fun i => (D n i).toLinearMap)
      (PolynomialFrameDerivatives.AffinePolynomialFrameDerivatives.commute p k B σ r hr hbase n) ≅
        PD.DeRham.PDDeRham.complex W (T n).ring (RingHom.ker (T n).reduction) (T n).dividedPowers :=
  PD.DeRhamTensor.PDDeRhamTensor.complexIso W (T n).ring σ (RingHom.ker (T n).reduction) (T n).dividedPowers
    (x n) (fun i => (D n i).toLinearMap) (D_eq_sum p k B σ r hr hbase n)
    (basis p k B σ r hr hbase n) (basis_apply p k B σ r hr hbase n)
    (PolynomialFrameDerivatives.AffinePolynomialFrameDerivatives.commute p k B σ r hr hbase n)

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.Affine.PolynomialFrameForms.AffinePolynomialFrameForms
