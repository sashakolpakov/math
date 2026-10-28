import OAI.NumberTheory.PadicHodge.IntegralComparison.Coherent.TensorNilpotence
import OAI.AlgebraicGeometry.SheafCohomology.Projective.IntrinsicDegree

/-! # Structure Dimension -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Coherent.StructureDimension.ProjectiveK

noncomputable section

/-! The actual structure-sheaf class belongs to the intrinsic-dimensional
part of the coherent Hilbert filtration over any infinite field. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry MonoidalCategory
open OAI.AlgebraicGeometry.SheafCohomology.Projective.IntrinsicDegree.Dimension

universe u
attribute [local instance] MvPolynomial.gradedAlgebra OAI.AlgebraicGeometry.SheafCohomology.Projective.Monoidal.Scheme.Modules.monoidalCategory

def coherentStructureModule (A : Scheme.{u}) : KTheory.Projective.CoherentModule A := by
  let O := OAI.AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj A
  letI : O.IsQuasicoherent := OAI.AlgebraicGeometry.SheafCohomology.Projective.InvertibleFinitePresentation.invertible_quasicoherent OAI.AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.isInvertible_unit
  letI : O.IsFiniteType :=
    OAI.AlgebraicGeometry.SheafCohomology.Projective.PolynomialQuotient.Dimension.isFiniteType_of_isLineBundle O (ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.isLineBundle_structureSheaf A)
  exact ⟨O, inferInstance, inferInstance⟩

variable {K : Type u} [Field K] {r : ℕ} {A : Scheme.{u}} [IsIntegral A]
  (f : A ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) K))
  [IsClosedImmersion f] (j : Fin (r + 1))

omit [AlgebraicGeometry.IsIntegral A] in
theorem coherentStructureHilbertPolynomial_spec :
    ∃ b : ℕ, ∀ n : ℕ, b ≤ n →
      (Module.finrank Γ(Spec (CommRingCat.of K), ⊤)
        ((OAI.AlgebraicGeometry.SheafCohomology.Projective.AdditiveCoproductSections.baseGlobalSectionsFunctor (f ≫ OAI.AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ)).obj
          ((Scheme.Modules.pullback f).obj
            (OAI.AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := K) j n))) : ℚ) =
        (HilbertFiltration.ProjectiveK.coherentHilbertPolynomial f j (coherentStructureModule A)).eval (n : ℚ) := by
  obtain ⟨b, hb⟩ := OAI.AlgebraicGeometry.FormalGeometry.Completion.Projective.Numerics.Construction.projectiveHilbertPolynomial_spec
    (OAI.AlgebraicGeometry.FormalGeometry.Completion.ClosedHilbertNumerics.Construction.coherentClosedDirectImage f (coherentStructureModule A).sheaf) j
  refine ⟨b, fun n hn => ?_⟩
  have he := (OAI.AlgebraicGeometry.SheafCohomology.Projective.PolynomialQuotient.Dimension.closedProjectiveTwistSectionReductionEquiv f j n).finrank_eq
  exact (congrArg (fun m : ℕ => (m : ℚ)) he).symm.trans (hb n hn)

theorem coherentStructureHilbertPolynomial_dimension
    (ρ : A ⟶ Spec (CommRingCat.of K)) [LocallyOfFiniteType ρ] :
    (HilbertFiltration.ProjectiveK.coherentHilbertPolynomial f j (coherentStructureModule A)).natDegree =
      OAI.AlgebraicGeometry.Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension ρ ∧
    0 < (HilbertFiltration.ProjectiveK.coherentHilbertPolynomial f j (coherentStructureModule A)).leadingCoeff := by
  obtain ⟨b, hb⟩ := coherentStructureHilbertPolynomial_spec f j
  exact OAI.AlgebraicGeometry.SheafCohomology.Projective.IntrinsicDegree.Dimension.closedProjective_Hilbert_intrinsicDegree ρ OAI.AlgebraicGeometry.FormalGeometry.Completion.Projective.Numerics.Construction.fieldSpec_sections_isField f j _ b hb

theorem coherentStructureClass_mem_hilbertFiltration
    (ρ : A ⟶ Spec (CommRingCat.of K)) [LocallyOfFiniteType ρ] :
    KTheory.Projective.coherentK0Class (coherentStructureModule A) ∈
      HilbertFiltration.ProjectiveK.coherentHilbertFiltration f j (OAI.AlgebraicGeometry.Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension ρ + 1) := by
  obtain ⟨hd, hp⟩ := coherentStructureHilbertPolynomial_dimension f j ρ
  apply HilbertFiltration.ProjectiveK.coherentK0Class_mem_hilbertFiltration
  rw [Polynomial.degree_eq_natDegree (Polynomial.leadingCoeff_ne_zero.mp hp.ne'), hd]
  exact WithBot.coe_lt_coe.mpr (Nat.lt_succ_self _)

variable [Infinite K]

include f j in
theorem coherentTensorDifference_structure_dimension
    (ρ : A ⟶ Spec (CommRingCat.of K)) [LocallyOfFiniteType ρ]
    (L : A.Modules) (hL : OAI.AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.IsInvertible L) :
    (KTheory.Projective.coherentTensorDifference L hL ^ (OAI.AlgebraicGeometry.Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension ρ + 1))
      (KTheory.Projective.coherentK0Class (coherentStructureModule A)) = 0 :=
  TensorNilpotence.ProjectiveK.coherentTensorDifference_pow_eq_zero_of_hilbertFiltration f j L hL _ _
    (coherentStructureClass_mem_hilbertFiltration f j ρ)

include f j in
theorem coherentTensorDifference_mixed_structure_dimension
    (ρ : A ⟶ Spec (CommRingCat.of K)) [LocallyOfFiniteType ρ]
    (L M N : A.Modules) (hL : OAI.AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.IsInvertible L)
    (hM : OAI.AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.IsInvertible M) (hN : OAI.AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.IsInvertible N)
    (a b c : ℕ) (hd : OAI.AlgebraicGeometry.Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension ρ < a + b + c) :
    (KTheory.Projective.coherentTensorDifference L hL ^ a)
      ((KTheory.Projective.coherentTensorDifference M hM ^ b)
        ((KTheory.Projective.coherentTensorDifference N hN ^ c)
          (KTheory.Projective.coherentK0Class (coherentStructureModule A)))) = 0 :=
  TensorNilpotence.ProjectiveK.coherentTensorDifference_mixed_eq_zero f j L M N hL hM hN a b c _
    (Nat.succ_le_of_lt hd) _ (coherentStructureClass_mem_hilbertFiltration f j ρ)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Coherent.StructureDimension.ProjectiveK
