import OAI.NumberTheory.PadicHodge.IntegralComparison.Endomorphism.FiniteSumWeights
import OAI.NumberTheory.PadicHodge.IntegralComparison.Finite.FamilyOrbitPolynomial
import OAI.NumberTheory.PadicHodge.IntegralComparison.Finite.FamilyTensorNilpotence

/-! # Finite Sum Euler -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Endomorphism.FiniteSumEuler

noncomputable section

/-! Genuine multivariate Euler polynomials for the pullbacks along
finite combinations of algebraic endomorphisms. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.Finite.FamilyTensorNilpotence.ProjectiveK OAI.NumberTheory.PadicHodge.IntegralComparison.Endomorphism.EulerPolynomial
open OAI.NumberTheory.PadicHodge.IntegralComparison.Endomorphism.FiniteSumWeights.Tensor OAI.NumberTheory.PadicHodge.IntegralComparison.Finite.FamilyNewton.Family

universe u v
attribute [local instance] MvPolynomial.gradedAlgebra

variable {K : Type u} [Field K] [IsAlgClosed K]
  (A : Over (Spec (CommRingCat.of K))) [GrpObj A] [IsCommMonObj A]
  [IsProper A.hom] [Smooth A.hom] [GeometricallyIntegral A.hom]
  {r : ℕ} (e : A.left ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) K))
  [IsClosedImmersion e]

local instance : IsIntegral A.left := GeometricallyIntegral.isIntegral_of_subsingleton A.hom

theorem euler_pullback_power (L : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.left)
    (hsym : Nonempty ((L.pullback (GrpObj.inv (X := A)).left).sheaf ≅ L.sheaf))
    {ι : Type v} [Fintype ι] (f : ι → AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd A) (a : ι → ℕ) (m : ℕ) :
    Coherent.EulerIndex.ProjectiveK.coherentEuler e ((L.pullback (2 • ∑ i, a i • f i).toMul.hom.hom.left).tensorPower m).sheaf =
      Coherent.EulerIndex.ProjectiveK.coherentEulerIndex e (Finite.FamilyNewton.Family.ordered (fun t => EulerPolynomial.tensorEnd (FiniteSumTensor.factor A L f t))
        (fun t => FiniteSumTensor.weight a t * m) (Coherent.KTheory.Projective.coherentK0Class (Coherent.StructureDimension.ProjectiveK.coherentStructureModule A.left))) := by
  rw [← Coherent.TensorPowers.ProjectiveK.coherentEulerIndex_tensor_power_structure]
  change Coherent.EulerIndex.ProjectiveK.coherentEulerIndex e
    ((EulerPolynomial.tensorEnd (L.pullback (2 • ∑ i, a i • f i).toMul.hom.hom.left) ^ m) _) = _
  rw [FiniteSumTensor.tensorEnd_double_sum_power A L hsym f a m]

theorem exists_euler_polynomials (j : Fin (r + 1)) (L : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.left)
    (hsym : Nonempty ((L.pullback (GrpObj.inv (X := A)).left).sheaf ≅ L.sheaf))
    {ι : Type v} [Fintype ι] (f : ι → AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd A) :
    ∃ (P : (ι → ℕ) → Polynomial ℚ) (D : MvPolynomial ι ℚ),
      D.totalDegree ≤ 2 * AlgebraicGeometry.Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension A.hom ∧
      (∀ a, (P a).natDegree ≤ AlgebraicGeometry.Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension A.hom) ∧
      (∀ a (m : ℕ), (P a).eval (m : ℚ) =
        (Coherent.EulerIndex.ProjectiveK.coherentEuler e
          ((L.pullback (2 • ∑ i, a i • f i).toMul.hom.hom.left).tensorPower m).sheaf : ℚ)) ∧
      (∀ a, (P a).coeff (AlgebraicGeometry.Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension A.hom) =
        MvPolynomial.eval (fun i => (a i : ℚ)) D) := by
  let φ : Coherent.KTheory.Projective.CoherentK0 A.left →+ ℚ := (Int.castAddHom ℚ).comp (Coherent.EulerIndex.ProjectiveK.coherentEulerIndex e)
  let x := Coherent.KTheory.Projective.coherentK0Class (Coherent.StructureDimension.ProjectiveK.coherentStructureModule A.left)
  have hz (n : Fin (Fintype.card (ι × ι)) → ℕ)
      (hn : AlgebraicGeometry.Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension A.hom < ∑ i, n i) :
      Finite.FamilyNewton.Family.ordered (fun t => EulerPolynomial.tensorEnd (FiniteSumTensor.factor A L f t) - 1) n x = 0 :=
    Finite.FamilyTensorNilpotence.ProjectiveK.coherentTensorDifference_family_eq_zero e j (fun t => (FiniteSumTensor.factor A L f t).sheaf)
      (fun t => AlgebraicGeometry.Quotients.FiniteDescent.LineBundleFree.Construction.LineBundleCoherence.invertible (FiniteSumTensor.factor A L f t)) n
      (AlgebraicGeometry.Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension A.hom + 1) (Nat.succ_le_of_lt hn) x
      (Coherent.StructureDimension.ProjectiveK.coherentStructureClass_mem_hilbertFiltration e j A.hom)
  obtain ⟨P, D, hD, hP, hval, htop⟩ := Finite.FamilyOrbitPolynomial.Family.orbit_polynomials
    (fun t => EulerPolynomial.tensorEnd (FiniteSumTensor.factor A L f t)) φ x (AlgebraicGeometry.Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension A.hom) 2 hz
    FiniteSumWeights.Tensor.weightPolynomial FiniteSumWeights.Tensor.weightPolynomial_totalDegree FiniteSumTensor.weight FiniteSumWeights.Tensor.weightPolynomial_eval
  refine ⟨P, D, hD, hP, ?_, htop⟩
  intro a m
  rw [hval]
  exact congrArg (fun z : ℤ => (z : ℚ)) (euler_pullback_power A e L hsym f a m).symm

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Endomorphism.FiniteSumEuler
