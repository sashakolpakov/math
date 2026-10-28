import OAI.NumberTheory.PadicHodge.IntegralComparison.Frobenius.ShiftIsogeny
import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.MultiplicationDegree
import OAI.NumberTheory.PadicHodge.IntegralComparison.Finite.FlatGenericDegree
import OAI.AlgebraicGeometry.SheafCohomology.IntrinsicDimension
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.CyclePushforward
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.SmoothStalk
import OAI.AlgebraicGeometry.SheafCohomology.Projective.DominantResidueDegree

/-! # Degree Is -/

namespace OAI

noncomputable section

namespace NumberTheory.PadicHodge.IntegralComparison.Endomorphism.DegreeIs.Divisibility

/-! The actual generic degree of an integer shift divides the degree of
the positive multiplication map supplied by an integral annihilator.
All degrees are native residue-field extension degrees. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory
open scoped _root_.CategoryTheory.MonObj TensorProduct

open OAI.NumberTheory.PadicHodge.IntegralComparison.Frobenius.ShiftIsogeny OAI.NumberTheory.PadicHodge.IntegralComparison.Finite.FlatGenericDegree

variable {K : Type} [Field K] [IsAlgClosed K]
  (A : Over (Spec (CommRingCat.of K))) [GrpObj A] [IsCommMonObj A]
  [IsProper A.hom] [Smooth A.hom] [GeometricallyIntegral A.hom]

local instance : IsIntegral A.left :=
  GeometricallyIntegral.isIntegral_of_subsingleton A.hom

theorem multiplication_residueDegree_eq_power_dimension (m : ℕ) (hm : 0 < m) :
    ((𝟙 A : A ⟶ A) ^ m).left.residueDegree (genericPoint A.left) =
      m ^ (2 * AlgebraicGeometry.Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension A.hom) := by
  have : IsFinite (ArithmeticGeometry.OrdinaryLocus.Openness.DefinitionsTorsion.Construction.torsionScheme A m).hom := by
    change IsFinite (AlgebraicGeometry.AbelianScheme.TorsionQuotient.SubgroupFunctor.torsionScheme A m).hom
    exact AlgebraicGeometry.FormalGeometry.Completion.PositiveMultiplication.Construction.torsionScheme_positive_finite A m hm
  have : IsFinite ((𝟙 A : A ⟶ A) ^ m).left := AlgebraicGeometry.FormalGeometry.Completion.PositiveMultiplication.Construction.multiplication_positive_isFinite A m hm
  obtain ⟨hs, hf⟩ := ArithmeticGeometry.OrdinaryLocus.Openness.FieldMultiplicationFlat.Construction.surjective_flat_multiplication_of_isFinite A m
  have : Surjective ((𝟙 A : A ⟶ A) ^ m).left := hs
  have : Flat ((𝟙 A : A ⟶ A) ^ m).left := hf
  rw [← Finite.FlatGenericDegree.finiteFlat_finrank_generic_eq_residueDegree _ (fun x => by
    have := AlgebraicGeometry.Quotients.FiniteDescent.SmoothStalk.Construction.SmoothStalkFactorial.stalk A.hom x
    infer_instance)]
  exact ArithmeticGeometry.OrdinaryLocus.Openness.MultiplicationDegree.Construction.multiplication_finrank_eq_power_dimension A m hm _
    (AlgebraicGeometry.SheafCohomology.IntrinsicDimension.Projective.topologicalKrullDim_eq_schemeTranscendenceDimension A.hom) _

theorem shift_degree_dvd_annihilator_value
    (f : AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd A) (Q : Polynomial ℤ)
    (hQf : Polynomial.aeval f Q = 0) (n : ℕ) (hn : 0 < Q.eval (n : ℤ)) :
    (((n : AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd A) - f).toMul.hom.hom.left.residueDegree (genericPoint A.left) : ℤ) ∣
      Q.eval (n : ℤ) ^ (2 * AlgebraicGeometry.Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension A.hom) := by
  let m := (Q.eval (n : ℤ)).toNat
  have hm : 0 < m := by dsimp [m]; omega
  have hmQ : (m : ℤ) = Q.eval (n : ℤ) := Int.toNat_of_nonneg hn.le
  obtain ⟨g, hg⟩ := Frobenius.ShiftIsogeny.integral_shift_factor f Q hQf n
  let s := ((n : AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd A) - f).toMul.hom.hom
  let t := g.toMul.hom.hom
  have he : s.left ≫ t.left = ((𝟙 A : A ⟶ A) ^ m).left := by
    have h := congrArg (fun z : AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd A => z.toMul.hom.hom.left) hg
    have hmR : (m : AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd A) = ↑(Q.eval (n : ℤ)) := by
      rw [← hmQ, Int.cast_natCast]
    rw [← hmR] at h
    change s.left ≫ t.left = (m : AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd A).toMul.hom.hom.left at h
    rw [← nsmul_one m, AlgebraicGeometry.FormalGeometry.Completion.Multiplication.Construction.algebraicEnd_nsmul_hom] at h
    exact h
  have hd : s.left.residueDegree (genericPoint A.left) ∣
      m ^ (2 * AlgebraicGeometry.Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension A.hom) := by
    rw [← multiplication_residueDegree_eq_power_dimension A m hm, ← he,
      AlgebraicGeometry.IntersectionTheory.ProjectionFormula.CyclePushforward.residueDegree_comp]
    exact dvd_mul_left _ _
  have hi : (s.left.residueDegree (genericPoint A.left) : ℤ) ∣
      (m : ℤ) ^ (2 * AlgebraicGeometry.Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension A.hom) := by exact_mod_cast hd
  rw [hmQ] at hi
  exact hi

theorem shift_degree_eventually_dvd_annihilator
    (f : AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd A) (Q : Polynomial ℤ) (hQ : Q.Monic)
    (hQf : Polynomial.aeval f Q = 0) :
    ∃ b : ℕ, ∀ n : ℕ, b ≤ n →
      (((n : AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd A) - f).toMul.hom.hom.left.residueDegree (genericPoint A.left) : ℤ) ∣
        Q.eval (n : ℤ) ^ (2 * AlgebraicGeometry.Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension A.hom) := by
  obtain ⟨b, hb⟩ := Frobenius.ShiftIsogeny.monic_eventually_positive Q hQ
  exact ⟨b, fun n hn => shift_degree_dvd_annihilator_value A f Q hQf n (hb n hn)⟩

end NumberTheory.PadicHodge.IntegralComparison.Endomorphism.DegreeIs.Divisibility

namespace NumberTheory.PadicHodge.IntegralComparison.Endomorphism.DegreeIs.Scalar

/-! Multiplying an actual endomorphism by a positive integer multiplies
its generic residue degree by the native degree of the multiplication map. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

open OAI.NumberTheory.PadicHodge.IntegralComparison.Endomorphism.DegreeIs.Divisibility
open OAI.AlgebraicGeometry.SheafCohomology.Projective.DominantResidueDegree.Dimension

variable {K : Type} [Field K] [IsAlgClosed K]
  (A : Over (Spec (CommRingCat.of K))) [GrpObj A] [IsCommMonObj A]
  [IsProper A.hom] [Smooth A.hom] [GeometricallyIntegral A.hom]

local instance : IsIntegral A.left :=
  GeometricallyIntegral.isIntegral_of_subsingleton A.hom

omit [IsAlgClosed K] [IsProper A.hom] [Smooth A.hom] [GeometricallyIntegral A.hom] in
theorem nsmul_underlying_comp (f : AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd A) (m : ℕ) :
    (m • f).toMul.hom.hom.left =
      f.toMul.hom.hom.left ≫ ((𝟙 A : A ⟶ A) ^ m).left := by
  rw [nsmul_eq_mul]
  have h := congrArg (fun t : A ⟶ A => t.left)
    (AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.algebraicEnd_mul_apply A (m : AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd A) f)
  rw [← nsmul_one m, AlgebraicGeometry.FormalGeometry.Completion.Multiplication.Construction.algebraicEnd_nsmul_hom] at h
  have h1 : (1 : AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd A).toMul.hom.hom = 𝟙 A := rfl
  simpa only [nsmul_one, h1, Over.comp_left] using h

theorem nsmul_isFinite (f : AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd A) [IsFinite f.toMul.hom.hom.left]
    (m : ℕ) (hm : 0 < m) : IsFinite (m • f).toMul.hom.hom.left := by
  rw [nsmul_underlying_comp A f m]
  have : IsFinite ((𝟙 A : A ⟶ A) ^ m).left := AlgebraicGeometry.FormalGeometry.Completion.PositiveMultiplication.Construction.multiplication_positive_isFinite A m hm
  infer_instance

theorem nsmul_isDominant (f : AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd A) [IsDominant f.toMul.hom.hom.left]
    (m : ℕ) (hm : 0 < m) : IsDominant (m • f).toMul.hom.hom.left := by
  rw [nsmul_underlying_comp A f m]
  have : IsFinite ((𝟙 A : A ⟶ A) ^ m).left := AlgebraicGeometry.FormalGeometry.Completion.PositiveMultiplication.Construction.multiplication_positive_isFinite A m hm
  have : Surjective ((𝟙 A : A ⟶ A) ^ m).left :=
    (ArithmeticGeometry.OrdinaryLocus.Openness.FieldMultiplicationFlat.Construction.surjective_flat_multiplication_of_isFinite A m).1
  infer_instance

theorem nsmul_residueDegree (f : AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd A) [IsDominant f.toMul.hom.hom.left]
    (m : ℕ) (hm : 0 < m) :
    (m • f).toMul.hom.hom.left.residueDegree (genericPoint A.left) =
      m ^ (2 * AlgebraicGeometry.Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension A.hom) *
        f.toMul.hom.hom.left.residueDegree (genericPoint A.left) := by
  rw [nsmul_underlying_comp A f m, AlgebraicGeometry.IntersectionTheory.ProjectionFormula.CyclePushforward.residueDegree_comp,
    AlgebraicGeometry.SheafCohomology.Projective.DominantFunctionField.Dimension.dominant_genericPoint f.toMul.hom.hom.left,
    Divisibility.multiplication_residueDegree_eq_power_dimension A m hm]

end NumberTheory.PadicHodge.IntegralComparison.Endomorphism.DegreeIs.Scalar

namespace NumberTheory.PadicHodge.IntegralComparison.Endomorphism.DegreeIs.Product

/-! The native generic residue degree is multiplicative on actual
finite dominant algebraic endomorphisms. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.SheafCohomology.Projective.DominantResidueDegree.Dimension

variable {K : Type} [Field K] [IsAlgClosed K]
  (A : Over (Spec (CommRingCat.of K))) [GrpObj A] [IsCommMonObj A]
  [GeometricallyIntegral A.hom]

local instance : IsIntegral A.left :=
  GeometricallyIntegral.isIntegral_of_subsingleton A.hom

omit [IsAlgClosed K] [GeometricallyIntegral A.hom] in
theorem mul_isFinite (f g : AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd A)
    [IsFinite f.toMul.hom.hom.left] [IsFinite g.toMul.hom.hom.left] :
    IsFinite (f * g).toMul.hom.hom.left := by
  change IsFinite (g.toMul.hom.hom.left ≫ f.toMul.hom.hom.left)
  infer_instance

omit [IsAlgClosed K] [GeometricallyIntegral A.hom] in
theorem mul_isDominant (f g : AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd A)
    [IsDominant f.toMul.hom.hom.left] [IsDominant g.toMul.hom.hom.left] :
    IsDominant (f * g).toMul.hom.hom.left := by
  change IsDominant (g.toMul.hom.hom.left ≫ f.toMul.hom.hom.left)
  infer_instance

omit [IsAlgClosed K] in
theorem mul_residueDegree (f g : AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd A) [IsDominant g.toMul.hom.hom.left] :
    (f * g).toMul.hom.hom.left.residueDegree (genericPoint A.left) =
      f.toMul.hom.hom.left.residueDegree (genericPoint A.left) *
        g.toMul.hom.hom.left.residueDegree (genericPoint A.left) := by
  change (g.toMul.hom.hom.left ≫ f.toMul.hom.hom.left).residueDegree _ = _
  rw [AlgebraicGeometry.IntersectionTheory.ProjectionFormula.CyclePushforward.residueDegree_comp, AlgebraicGeometry.SheafCohomology.Projective.DominantFunctionField.Dimension.dominant_genericPoint g.toMul.hom.hom.left]

omit [IsAlgClosed K] [GeometricallyIntegral A.hom] in
theorem family_mul_sum {ι κ : Type*} [Fintype ι] [Fintype κ]
    (f : ι → AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd A) (g : κ → AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd A) (a : ι → ℕ) (b : κ → ℕ) :
    (∑ t : ι × κ, (a t.1 * b t.2) • (f t.1 * g t.2)) =
      (∑ i, a i • f i) * ∑ j, b j • g j := by
  rw [Fintype.sum_prod_type, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [nsmul_eq_mul, Nat.cast_mul]
  rw [mul_assoc, ← mul_assoc (b j : AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd A), Nat.cast_comm (b j) (f i)]
  simp only [mul_assoc]

end NumberTheory.PadicHodge.IntegralComparison.Endomorphism.DegreeIs.Product

end

end OAI
