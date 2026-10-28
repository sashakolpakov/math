import OAI.NumberTheory.PadicHodge.IntegralComparison.Endomorphism.DegreeUniqueness
import OAI.NumberTheory.PadicHodge.IntegralComparison.Endomorphism.DegreeIs
import OAI.NumberTheory.PadicHodge.IntegralComparison.DegreeProductCoordinates

/-! # Degree Law -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Endomorphism.DegreeLaw

noncomputable section

/-! Multiplicativity of the geometric degree polynomials, proved from
native generic residue degrees on independently shifted endomorphisms. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.Endomorphism.DegreeUniqueness OAI.NumberTheory.PadicHodge.IntegralComparison.Endomorphism.DegreeIs.Product
open OAI.NumberTheory.PadicHodge.IntegralComparison.DegreeProductCoordinates

universe v w
variable {K : Type} [Field K] [IsAlgClosed K]
  (A : Over (Spec (CommRingCat.of K))) [GrpObj A] [IsCommMonObj A]
  [IsProper A.hom] [Smooth A.hom] [GeometricallyIntegral A.hom]

local instance : IsIntegral A.left :=
  GeometricallyIntegral.isIntegral_of_subsingleton A.hom

def degreePolynomial {ι : Type v} [Fintype ι] (f : ι → AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd A) : MvPolynomial ι ℚ :=
  (FiniteSumDegree.exists_degree_polynomial A f).choose

theorem degreePolynomial_totalDegree {ι : Type v} [Fintype ι] (f : ι → AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd A) :
    (degreePolynomial A f).totalDegree ≤ 2 * AlgebraicGeometry.Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension A.hom :=
  (FiniteSumDegree.exists_degree_polynomial A f).choose_spec.1

theorem degreePolynomial_eval {ι : Type v} [Fintype ι] (f : ι → AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd A)
    (a : ι → ℕ) [IsFinite (∑ i, a i • f i).toMul.hom.hom.left]
    [IsDominant (∑ i, a i • f i).toMul.hom.hom.left] :
    MvPolynomial.eval (fun i => (a i : ℚ)) (degreePolynomial A f) =
      ((∑ i, a i • f i).toMul.hom.hom.left.residueDegree (genericPoint A.left) : ℚ) :=
  (FiniteSumDegree.exists_degree_polynomial A f).choose_spec.2 a
    inferInstance inferInstance

theorem degreePolynomial_mul {ι : Type v} {κ : Type w} [Fintype ι] [Fintype κ]
    (f : ι → AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd A) (g : κ → AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd A) :
    DegreeProductCoordinates.productSub (degreePolynomial A
      (fun t : Option ι × Option κ => DegreeUniqueness.withIdentity A f t.1 * DegreeUniqueness.withIdentity A g t.2)) =
    DegreeProductCoordinates.leftSub (degreePolynomial A (DegreeUniqueness.withIdentity A f)) *
      DegreeProductCoordinates.rightSub (degreePolynomial A (DegreeUniqueness.withIdentity A g)) := by
  apply MultivariateTailIdentity.eq_of_double_option_tail_eval
  intro z
  obtain ⟨b, hb⟩ := DegreeUniqueness.withIdentity_eventually_isogeny A f (fun i => z (.inl i))
  refine ⟨b, fun n hn => ?_⟩
  obtain ⟨c, hc⟩ := DegreeUniqueness.withIdentity_eventually_isogeny A g (fun j => z (.inr j))
  refine ⟨c, fun m hm => ?_⟩
  let a : Option ι → ℕ := fun i => Option.elim i n (fun j => z (.inl j))
  let b' : Option κ → ℕ := fun i => Option.elim i m (fun j => z (.inr j))
  let s : AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd A := ∑ i, a i • DegreeUniqueness.withIdentity A f i
  let t : AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd A := ∑ j, b' j • DegreeUniqueness.withIdentity A g j
  have : IsFinite s.toMul.hom.hom.left := (hb n hn).1
  have : IsDominant s.toMul.hom.hom.left := (hb n hn).2
  have : IsFinite t.toMul.hom.hom.left := (hc m hm).1
  have : IsDominant t.toMul.hom.hom.left := (hc m hm).2
  have he : (∑ ij : Option ι × Option κ,
      (a ij.1 * b' ij.2) • (DegreeUniqueness.withIdentity A f ij.1 * DegreeUniqueness.withIdentity A g ij.2)) = s * t :=
    DegreeIs.Product.family_mul_sum A (DegreeUniqueness.withIdentity A f) (DegreeUniqueness.withIdentity A g) a b'
  have : IsFinite (∑ ij : Option ι × Option κ,
      (a ij.1 * b' ij.2) • (DegreeUniqueness.withIdentity A f ij.1 * DegreeUniqueness.withIdentity A g ij.2)).toMul.hom.hom.left := by
    rw [he]
    exact DegreeIs.Product.mul_isFinite A s t
  have : IsDominant (∑ ij : Option ι × Option κ,
      (a ij.1 * b' ij.2) • (DegreeUniqueness.withIdentity A f ij.1 * DegreeUniqueness.withIdentity A g ij.2)).toMul.hom.hom.left := by
    rw [he]
    exact DegreeIs.Product.mul_isDominant A s t
  rw [DegreeProductCoordinates.eval_productSub, map_mul, DegreeProductCoordinates.eval_leftSub, DegreeProductCoordinates.eval_rightSub]
  simp only [DegreeProductCoordinates.leftIndex_point, DegreeProductCoordinates.rightIndex_point]
  change MvPolynomial.eval (fun ij : Option ι × Option κ => (a ij.1 : ℚ) * (b' ij.2 : ℚ)) _ =
    MvPolynomial.eval (fun i => (a i : ℚ)) _ * MvPolynomial.eval (fun j => (b' j : ℚ)) _
  simp only [← Nat.cast_mul]
  rw [degreePolynomial_eval, degreePolynomial_eval, degreePolynomial_eval, he]
  exact_mod_cast DegreeIs.Product.mul_residueDegree A s t

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Endomorphism.DegreeLaw
