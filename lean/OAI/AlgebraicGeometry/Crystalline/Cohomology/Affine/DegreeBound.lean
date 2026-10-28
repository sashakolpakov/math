import OAI.AlgebraicGeometry.Crystalline.Cohomology.Affine.Comparison
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Finite.PDForms

/-! # Degree Bound -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.Affine.DegreeBound.AffineDegreeBound

noncomputable section

/-! # The original completed affine PD complex vanishes above its coordinate rank -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u

variable (p : ℕ) [Fact p.Prime] (k B σ : Type u) [Field k] [CharP k p]
  [CommRing B] [Algebra k B]
  (r : MvPolynomial σ (WittVector p k) →+* B) (hr : Function.Surjective r)
  (hbase : r.comp (algebraMap (WittVector p k) (MvPolynomial σ (WittVector p k))) =
    (algebraMap k B).comp WittVector.constantCoeff) [Fintype σ]

local notation "W" => WittVector p k
local notation "Poly" => MvPolynomial σ W
local notation "Frame" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Affine.EnvelopeFrames.AffineEnvelopeFrames.frame p k B Poly r hr hbase
local notation "Tower" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Affine.EnvelopeFrames.AffineEnvelopeFrames.tower p k B Poly r hr hbase

theorem level_zero (n q : ℕ) (hq : Fintype.card σ < q)
    (ω : PD.DeRham.PDDeRham.Form W (Frame n).ring (RingHom.ker (Frame n).reduction)
      (Frame n).dividedPowers q) : ω = 0 := by
  apply Finite.PDForms.FinitePDForms.higher_form_eq_zero W (Frame n).ring
    (RingHom.ker (Frame n).reduction) (Frame n).dividedPowers
    (fun i => EnvelopeFrameUniversal.AffineEnvelopeFrameUniversal.coefficient p k B Poly r hr hbase n (MvPolynomial.X i))
    ?_ q hq ω
  have he : (fun i => PD.OneForms.PDOneForms.D W (Frame n).ring (RingHom.ker (Frame n).reduction)
      (Frame n).dividedPowers
      (EnvelopeFrameUniversal.AffineEnvelopeFrameUniversal.coefficient p k B Poly r hr hbase n (MvPolynomial.X i))) =
      PolynomialFrameForms.AffinePolynomialFrameForms.basis p k B σ r hr hbase n :=
    funext (fun i => (PolynomialFrameForms.AffinePolynomialFrameForms.basis_apply p k B σ r hr hbase n i).symm)
  rw [he]
  exact (PolynomialFrameForms.AffinePolynomialFrameForms.basis p k B σ r hr hbase n).span_eq

theorem completed_zero (q : ℕ) (hq : Fintype.card σ < q)
    (ω : PD.PDDeRham.CompletedForm p k B Tower q) : ω = 0 := by
  apply PD.PDDeRham.ext p k B Tower
  intro n
  rw [map_zero]
  exact level_zero p k B σ r hr hbase n q hq _

theorem term_isZero (q : ℕ) (hq : Fintype.card σ < q) :
    IsZero ((PD.PDDeRham.complex p k B Tower).X q) := by
  change IsZero (ModuleCat.of W (PD.PDDeRham.CompletedForm p k B Tower q))
  have : Subsingleton (PD.PDDeRham.CompletedForm p k B Tower q) :=
    ⟨fun x y => (completed_zero p k B σ r hr hbase q hq x).trans
      (completed_zero p k B σ r hr hbase q hq y).symm⟩
  exact ModuleCat.isZero_of_subsingleton _

theorem lifted_term_isZero (q : ℕ) (hq : Fintype.card σ < q) :
    IsZero ((Comparison.AffineCrystallineComparison.completedComplex p k B σ r hr hbase).X q) :=
  (Comparison.AffineCrystallineComparison.largeLift p k).map_isZero
    ((PolynomialSheafResolution.CrystallinePolynomialSheafResolution.coefficientLift p k).map_isZero
      (term_isZero p k B σ r hr hbase q hq))

theorem homology_isZero (q : ℕ) (hq : Fintype.card σ < q) :
    IsZero ((Comparison.AffineCrystallineComparison.completedComplex p k B σ r hr hbase).homology q) :=
  (HomologicalComplex.ExactAt.of_isZero (lifted_term_isZero p k B σ r hr hbase q hq)).isZero_homology

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.Affine.DegreeBound.AffineDegreeBound
