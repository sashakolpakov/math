import OAI.NumberTheory.PadicHodge.IntegralComparison.Endomorphism.EulerPolynomial
import OAI.NumberTheory.PadicHodge.IntegralComparison.Coherent.HilbertLeadingDifference
import OAI.NumberTheory.PadicHodge.IntegralComparison.Finite.PullbackHilbert
import OAI.NumberTheory.PadicHodge.IntegralComparison.Finite.PushforwardHilbert
import OAI.NumberTheory.PadicHodge.IntegralComparison.SymmetricProjectiveEmbedding
import OAI.NumberTheory.PadicHodge.IntegralComparison.Frobenius.ShiftIsogeny
import OAI.AlgebraicGeometry.SheafCohomology.Projective.DominantResidueDegree

/-! # Degree Polynomial -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Endomorphism.DegreePolynomial

noncomputable section

/-! The degree polynomial of an actual abelian-scheme endomorphism.
Its normalization comes from the positive leading coefficient of the
structure-sheaf Hilbert polynomial. At every finite dominant shift it
computes the actual generic residue degree of that shift. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.Endomorphism.EulerPolynomial
  AlgebraicGeometry.SheafCohomology.Projective.DominantResidueDegree.Dimension

attribute [local instance] MvPolynomial.gradedAlgebra

variable {K : Type} [Field K] [IsAlgClosed K]
  (A : Over (Spec (CommRingCat.of K))) [GrpObj A] [IsCommMonObj A]
  [IsProper A.hom] [Smooth A.hom] [GeometricallyIntegral A.hom]

local instance : IsIntegral A.left :=
  GeometricallyIntegral.isIntegral_of_subsingleton A.hom

theorem exists_degree_polynomial_of_symmetric_embedding
    {r : ℕ}
    (a : A.left ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) K))
    [IsClosedImmersion a] (j : Fin (r + 1))
    (ha : a ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ = A.hom)
    (hsym : Nonempty (((Coherent.EulerHilbert.ProjectiveK.projectiveLineBundle a j).pullback
      (GrpObj.inv (X := A)).left).sheaf ≅ (Coherent.EulerHilbert.ProjectiveK.projectiveLineBundle a j).sheaf))
    (f : AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd A) :
    ∃ D : Polynomial ℚ, D.Monic ∧
      D.natDegree = 2 * AlgebraicGeometry.Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension A.hom ∧
      ∀ n : ℕ,
        IsFinite ((n : AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd A) - f).toMul.hom.hom.left →
        IsDominant ((n : AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd A) - f).toMul.hom.hom.left →
        D.eval (n : ℚ) =
          (((n : AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd A) - f).toMul.hom.hom.left.residueDegree
            (genericPoint A.left) : ℚ) := by
  have : IsIntegral A.left := GeometricallyIntegral.isIntegral_of_subsingleton A.hom
  have : A.left.IsSeparated := by
    constructor
    rw [← CategoryTheory.Limits.terminal.comp_from A.hom]
    infer_instance
  let d := AlgebraicGeometry.Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension A.hom
  let H := Coherent.HilbertFiltration.ProjectiveK.coherentHilbertPolynomial a j (Coherent.StructureDimension.ProjectiveK.coherentStructureModule A.left)
  let c := H.leadingCoeff
  have hc : 0 < c := (Coherent.StructureDimension.ProjectiveK.coherentStructureHilbertPolynomial_dimension a j A.hom).2
  obtain ⟨P, D₀, hD₀, _, hP, htop, hlead⟩ :=
    EulerPolynomial.exists_euler_polynomials A a j (Coherent.EulerHilbert.ProjectiveK.projectiveLineBundle a j) hsym f
  have hD₀top : D₀.coeff (2 * d) = c := by
    exact hlead.trans (Coherent.HilbertLeadingDifference.ProjectiveK.coherentStructureHilbert_leadingCoeff_eq_difference a j A.hom).symm
  let D := Polynomial.C c⁻¹ * D₀
  have hD : D.natDegree ≤ 2 * d :=
    (Polynomial.natDegree_C_mul_le c⁻¹ D₀).trans hD₀
  have hDtop : D.coeff (2 * d) = 1 := by
    change (Polynomial.C c⁻¹ * D₀).coeff (2 * d) = 1
    rw [Polynomial.coeff_C_mul, hD₀top, inv_mul_cancel₀ hc.ne']
  refine ⟨D, Polynomial.monic_of_natDegree_le_of_coeff_eq_one _ hD hDtop,
    Polynomial.natDegree_eq_of_le_of_coeff_ne_zero hD (hDtop.trans_ne one_ne_zero), ?_⟩
  intro n hfinite hdominant
  let g : A.left ⟶ A.left := ((n : AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd A) - f).toMul.hom.hom.left
  have : IsFinite g := hfinite
  have : IsDominant g := hdominant
  have hg : g ≫ A.hom = A.hom := ((n : AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd A) - f).toMul.hom.hom.w
  have hnormal (x : A.left) : IsIntegrallyClosed (A.left.presheaf.stalk x) := by
    have := AlgebraicGeometry.Quotients.FiniteDescent.SmoothStalk.Construction.SmoothStalkFactorial.stalk A.hom x
    infer_instance
  have hpoly := Finite.PullbackHilbert.ProjectiveK.polynomial_eq_finitePushforward_hilbert a j A.hom ha g hg (P n) (hP n)
  have hdegree := Finite.PushforwardHilbert.finitePushforward_degree_leadingCoeff
    g hnormal a A.hom j
  dsimp only at hdegree
  rw [AlgebraicGeometry.SheafCohomology.Projective.DominantResidueDegree.Dimension.dominantFunctionField_finrank_eq_residueDegree g] at hdegree
  have hdegree' :
      (Coherent.HilbertFiltration.ProjectiveK.coherentHilbertPolynomial a j
        (Finite.PullbackHilbert.ProjectiveK.coherentFinitePushforward g (Coherent.StructureDimension.ProjectiveK.coherentStructureModule A.left))).natDegree = d ∧
      (Coherent.HilbertFiltration.ProjectiveK.coherentHilbertPolynomial a j
        (Finite.PullbackHilbert.ProjectiveK.coherentFinitePushforward g (Coherent.StructureDimension.ProjectiveK.coherentStructureModule A.left))).leadingCoeff =
        (g.residueDegree (genericPoint A.left) : ℚ) * c := hdegree
  have hval : D₀.eval (n : ℚ) =
      (g.residueDegree (genericPoint A.left) : ℚ) * c := by
    rw [← htop n, hpoly]
    change (Coherent.HilbertFiltration.ProjectiveK.coherentHilbertPolynomial a j
      (Finite.PullbackHilbert.ProjectiveK.coherentFinitePushforward g (Coherent.StructureDimension.ProjectiveK.coherentStructureModule A.left))).coeff d = _
    rw [← hdegree'.1, Polynomial.coeff_natDegree]
    exact hdegree'.2
  change (Polynomial.C c⁻¹ * D₀).eval (n : ℚ) = _
  rw [Polynomial.eval_mul, Polynomial.eval_C, hval]
  field_simp [hc.ne']
  rfl

theorem exists_degree_polynomial (f : AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd A) :
    ∃ D : Polynomial ℚ, D.Monic ∧
      D.natDegree = 2 * AlgebraicGeometry.Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension A.hom ∧
      ∀ n : ℕ,
        IsFinite ((n : AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd A) - f).toMul.hom.hom.left →
        IsDominant ((n : AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd A) - f).toMul.hom.hom.left →
        D.eval (n : ℚ) =
          (((n : AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd A) - f).toMul.hom.hom.left.residueDegree
            (genericPoint A.left) : ℚ) := by
  obtain ⟨r, a, ha, hbase, hsym⟩ :=
    SymmetricProjectiveEmbedding.exists_symmetric_projective_embedding A
  have : IsClosedImmersion a := ha
  exact exists_degree_polynomial_of_symmetric_embedding A a 0 hbase hsym f

theorem exists_degree_polynomial_on_tail (f : AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd A) :
    ∃ D : Polynomial ℚ, D.Monic ∧
      D.natDegree = 2 * AlgebraicGeometry.Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension A.hom ∧
      ∃ b : ℕ, ∀ n : ℕ, b ≤ n →
        D.eval (n : ℚ) =
          (((n : AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd A) - f).toMul.hom.hom.left.residueDegree
            (genericPoint A.left) : ℚ) := by
  obtain ⟨D, hD, hd, he⟩ := exists_degree_polynomial A f
  obtain ⟨b, hb⟩ := Frobenius.ShiftIsogeny.endomorphism_shift_eventually_isogeny A f
  refine ⟨D, hD, hd, b, fun n hn => ?_⟩
  obtain ⟨hf, hs, _⟩ := hb n hn
  have : Surjective ((n : AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd A) - f).toMul.hom.hom.left := hs
  exact he n hf inferInstance

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Endomorphism.DegreePolynomial
