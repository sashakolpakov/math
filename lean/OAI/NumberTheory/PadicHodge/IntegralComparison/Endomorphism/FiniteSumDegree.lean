import OAI.NumberTheory.PadicHodge.IntegralComparison.Endomorphism.FiniteSumEuler
import OAI.NumberTheory.PadicHodge.IntegralComparison.Endomorphism.DegreeIs
import OAI.NumberTheory.PadicHodge.IntegralComparison.Endomorphism.DegreePolynomial

/-! # Finite Sum Degree -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Endomorphism.FiniteSumDegree

noncomputable section

/-! A genuine multivariate polynomial for the geometric degree of a
finite combination of endomorphisms of an abelian variety. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.Endomorphism.DegreeIs.Scalar

universe v
attribute [local instance] MvPolynomial.gradedAlgebra

variable {K : Type} [Field K] [IsAlgClosed K]
  (A : Over (Spec (CommRingCat.of K))) [GrpObj A] [IsCommMonObj A]
  [IsProper A.hom] [Smooth A.hom] [GeometricallyIntegral A.hom]

local instance : IsIntegral A.left :=
  GeometricallyIntegral.isIntegral_of_subsingleton A.hom

theorem exists_degree_polynomial_of_symmetric_embedding
    {r : ℕ}
    (e : A.left ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) K))
    [IsClosedImmersion e] (j : Fin (r + 1))
    (he : e ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ = A.hom)
    (hsym : Nonempty (((Coherent.EulerHilbert.ProjectiveK.projectiveLineBundle e j).pullback
      (GrpObj.inv (X := A)).left).sheaf ≅ (Coherent.EulerHilbert.ProjectiveK.projectiveLineBundle e j).sheaf))
    {ι : Type v} [Fintype ι] (f : ι → AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd A) :
    ∃ D : MvPolynomial ι ℚ,
      D.totalDegree ≤ 2 * AlgebraicGeometry.Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension A.hom ∧
      ∀ a : ι → ℕ,
        IsFinite (∑ i, a i • f i).toMul.hom.hom.left →
        IsDominant (∑ i, a i • f i).toMul.hom.hom.left →
        MvPolynomial.eval (fun i => (a i : ℚ)) D =
          ((∑ i, a i • f i).toMul.hom.hom.left.residueDegree
            (genericPoint A.left) : ℚ) := by
  have : A.left.IsSeparated := by
    constructor
    rw [← CategoryTheory.Limits.terminal.comp_from A.hom]
    infer_instance
  let d := AlgebraicGeometry.Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension A.hom
  let H := Coherent.HilbertFiltration.ProjectiveK.coherentHilbertPolynomial e j (Coherent.StructureDimension.ProjectiveK.coherentStructureModule A.left)
  let c := H.leadingCoeff
  let q : ℚ := 2 ^ (2 * d)
  have hc : 0 < c := (Coherent.StructureDimension.ProjectiveK.coherentStructureHilbertPolynomial_dimension e j A.hom).2
  have hq : q ≠ 0 := pow_ne_zero _ (by norm_num)
  obtain ⟨P, D₀, hD₀, _, hP, htop⟩ :=
    FiniteSumEuler.exists_euler_polynomials A e j
      (Coherent.EulerHilbert.ProjectiveK.projectiveLineBundle e j) hsym f
  let D := MvPolynomial.C ((q * c)⁻¹) * D₀
  have hD : D.totalDegree ≤ 2 * d := by
    exact (MvPolynomial.totalDegree_mul _ _).trans
      (by simpa only [MvPolynomial.totalDegree_C, zero_add] using hD₀)
  refine ⟨D, hD, ?_⟩
  intro a hfinite hdominant
  let s : AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd A := ∑ i, a i • f i
  have : IsFinite s.toMul.hom.hom.left := hfinite
  have : IsDominant s.toMul.hom.hom.left := hdominant
  let g := (2 • s).toMul.hom.hom.left
  have : IsFinite g := DegreeIs.Scalar.nsmul_isFinite A s 2 (by norm_num)
  have : IsDominant g := DegreeIs.Scalar.nsmul_isDominant A s 2 (by norm_num)
  have hg : g ≫ A.hom = A.hom := (2 • s).toMul.hom.hom.w
  have hnormal (x : A.left) : IsIntegrallyClosed (A.left.presheaf.stalk x) := by
    have := AlgebraicGeometry.Quotients.FiniteDescent.SmoothStalk.Construction.SmoothStalkFactorial.stalk A.hom x
    infer_instance
  have hpoly := Finite.PullbackHilbert.ProjectiveK.polynomial_eq_finitePushforward_hilbert e j A.hom he g hg (P a) (hP a)
  have hdegree := Finite.PushforwardHilbert.finitePushforward_degree_leadingCoeff
    g hnormal e A.hom j
  dsimp only at hdegree
  rw [AlgebraicGeometry.SheafCohomology.Projective.DominantResidueDegree.Dimension.dominantFunctionField_finrank_eq_residueDegree g] at hdegree
  have hdegree' :
      (Coherent.HilbertFiltration.ProjectiveK.coherentHilbertPolynomial e j
        (Finite.PullbackHilbert.ProjectiveK.coherentFinitePushforward g (Coherent.StructureDimension.ProjectiveK.coherentStructureModule A.left))).natDegree = d ∧
      (Coherent.HilbertFiltration.ProjectiveK.coherentHilbertPolynomial e j
        (Finite.PullbackHilbert.ProjectiveK.coherentFinitePushforward g (Coherent.StructureDimension.ProjectiveK.coherentStructureModule A.left))).leadingCoeff =
        (g.residueDegree (genericPoint A.left) : ℚ) * c := hdegree
  have hval : MvPolynomial.eval (fun i => (a i : ℚ)) D₀ =
      (g.residueDegree (genericPoint A.left) : ℚ) * c := by
    rw [← htop a, hpoly]
    change (Coherent.HilbertFiltration.ProjectiveK.coherentHilbertPolynomial e j
      (Finite.PullbackHilbert.ProjectiveK.coherentFinitePushforward g (Coherent.StructureDimension.ProjectiveK.coherentStructureModule A.left))).coeff d = _
    rw [← hdegree'.1, Polynomial.coeff_natDegree]
    exact hdegree'.2
  have hscalar : (g.residueDegree (genericPoint A.left) : ℚ) =
      q * (s.toMul.hom.hom.left.residueDegree (genericPoint A.left) : ℚ) := by
    dsimp only [g, q, d]
    exact_mod_cast DegreeIs.Scalar.nsmul_residueDegree A s 2 (by norm_num)
  change MvPolynomial.eval (fun i => (a i : ℚ))
    (MvPolynomial.C ((q * c)⁻¹) * D₀) = _
  rw [map_mul, MvPolynomial.eval_C, hval, hscalar]
  field_simp [hc.ne', hq]
  ring

theorem exists_degree_polynomial {ι : Type v} [Fintype ι] (f : ι → AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd A) :
    ∃ D : MvPolynomial ι ℚ,
      D.totalDegree ≤ 2 * AlgebraicGeometry.Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension A.hom ∧
      ∀ a : ι → ℕ,
        IsFinite (∑ i, a i • f i).toMul.hom.hom.left →
        IsDominant (∑ i, a i • f i).toMul.hom.hom.left →
        MvPolynomial.eval (fun i => (a i : ℚ)) D =
          ((∑ i, a i • f i).toMul.hom.hom.left.residueDegree
            (genericPoint A.left) : ℚ) := by
  obtain ⟨r, e, he, hbase, hsym⟩ :=
    SymmetricProjectiveEmbedding.exists_symmetric_projective_embedding A
  have : IsClosedImmersion e := he
  exact exists_degree_polynomial_of_symmetric_embedding A e 0 hbase hsym f

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Endomorphism.FiniteSumDegree
