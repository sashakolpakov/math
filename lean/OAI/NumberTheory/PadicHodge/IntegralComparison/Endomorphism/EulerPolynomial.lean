import OAI.NumberTheory.PadicHodge.IntegralComparison.Endomorphism.PullbackPowers
import OAI.NumberTheory.PadicHodge.IntegralComparison.MixedOrbitPolynomial
import OAI.NumberTheory.PadicHodge.IntegralComparison.Coherent.TensorPowers

/-! # Euler Polynomial -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Endomorphism.EulerPolynomial

noncomputable section

/-! Actual coherent Euler polynomials of the powers of `([n] - f)^*L`.
The degree bounds use the intrinsic dimension and the proved tensor
difference filtration; the pullbacks and Euler characteristics are the
original geometric constructions. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory MonoidalCategory

open OAI.NumberTheory.PadicHodge.IntegralComparison.Coherent.TensorPowers.ProjectiveK OAI.NumberTheory.PadicHodge.IntegralComparison.Endomorphism.PullbackPowers

universe u

attribute [local instance] MvPolynomial.gradedAlgebra AlgebraicGeometry.SheafCohomology.Projective.Monoidal.Scheme.Modules.monoidalCategory
  AlgebraicGeometry.SheafCohomology.Projective.Monoidal.Scheme.Modules.symmetricCategory

abbrev tensorEnd {X : Scheme.{u}} (L : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X) : AddMonoid.End (Coherent.KTheory.Projective.CoherentK0 X) :=
  Coherent.KTheory.Projective.coherentTensorEnd L.sheaf (AlgebraicGeometry.Quotients.FiniteDescent.LineBundleFree.Construction.LineBundleCoherence.invertible L)

theorem tensorEnd_tensor {X : Scheme.{u}} (L M : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X) :
    tensorEnd (L.tensor M) = tensorEnd L * tensorEnd M := by
  symm
  change (Coherent.KTheory.Projective.coherentTensorK0 L.sheaf _).comp (Coherent.KTheory.Projective.coherentTensorK0 M.sheaf _) = _
  rw [Coherent.KTheory.Projective.coherentTensorK0_comp]
  exact Coherent.KTheory.Projective.coherentTensorK0_congr _ _
    ((β_ M.sheaf L.sheaf) ≪≫ AlgebraicGeometry.Quotients.FiniteDescent.MonoidalLine.Construction.MonoidalLineBundles.tensorIso L.sheaf M.sheaf)

theorem tensorEnd_commute {X : Scheme.{u}} (L M : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X) :
    Commute (tensorEnd L) (tensorEnd M) :=
  Coherent.KTheory.Projective.coherentTensorK0_commute L.sheaf M.sheaf
    (AlgebraicGeometry.Quotients.FiniteDescent.LineBundleFree.Construction.LineBundleCoherence.invertible L) (AlgebraicGeometry.Quotients.FiniteDescent.LineBundleFree.Construction.LineBundleCoherence.invertible M)

theorem tensorEnd_power {X : Scheme.{u}} (L : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X) (m : ℕ) :
    tensorEnd (L.tensorPower m) = tensorEnd L ^ m :=
  (Coherent.TensorPowers.ProjectiveK.coherentTensorEnd_power L m).symm

variable {K : Type u} [Field K] [IsAlgClosed K]
  (A : Over (Spec (CommRingCat.of K))) [GrpObj A] [IsCommMonObj A]
  [IsProper A.hom] [Smooth A.hom] [GeometricallyIntegral A.hom]

theorem tensorEnd_pullback (L : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.left)
    (hsym : Nonempty ((L.pullback (GrpObj.inv (X := A)).left).sheaf ≅ L.sheaf))
    (f : AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd A) (n : ℕ) :
    tensorEnd (L.pullback ((n : AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd A) - f).toMul.hom.hom.left) =
      tensorEnd L ^ (n * n) * tensorEnd (PullbackPowers.linearBundle A L f) ^ n *
        tensorEnd (L.pullback f.toMul.hom.hom.left) := by
  obtain ⟨e⟩ := PullbackPowers.pullback_iso A L hsym f n
  have h := Coherent.KTheory.Projective.coherentTensorK0_congr
    (AlgebraicGeometry.Quotients.FiniteDescent.LineBundleFree.Construction.LineBundleCoherence.invertible (L.pullback ((n : AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd A) - f).toMul.hom.hom.left))
    (AlgebraicGeometry.Quotients.FiniteDescent.LineBundleFree.Construction.LineBundleCoherence.invertible (PullbackPowers.tensorOrbit A L f n)) e
  change tensorEnd (L.pullback ((n : AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd A) - f).toMul.hom.hom.left) =
    tensorEnd (PullbackPowers.tensorOrbit A L f n) at h
  rw [h]
  simp only [PullbackPowers.tensorOrbit, tensorEnd_tensor, tensorEnd_power]

theorem tensorEnd_pullback_power (L : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.left)
    (hsym : Nonempty ((L.pullback (GrpObj.inv (X := A)).left).sheaf ≅ L.sheaf))
    (f : AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd A) (n m : ℕ) :
    tensorEnd (L.pullback ((n : AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd A) - f).toMul.hom.hom.left) ^ m =
      tensorEnd L ^ (n * n * m) * tensorEnd (PullbackPowers.linearBundle A L f) ^ (n * m) *
        tensorEnd (L.pullback f.toMul.hom.hom.left) ^ m := by
  rw [tensorEnd_pullback A L hsym f n]
  have h₁ := (tensorEnd_commute L (PullbackPowers.linearBundle A L f)).pow_pow (n * n) n
  have h₂ := ((tensorEnd_commute L (L.pullback f.toMul.hom.hom.left)).pow_left (n * n)).mul_left
    ((tensorEnd_commute (PullbackPowers.linearBundle A L f) (L.pullback f.toMul.hom.hom.left)).pow_left n)
  rw [h₂.mul_pow, h₁.mul_pow, ← pow_mul, ← pow_mul]

variable {r : ℕ}
  (e : A.left ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) K))
  [IsClosedImmersion e]

local instance : IsIntegral A.left :=
  GeometricallyIntegral.isIntegral_of_subsingleton A.hom

theorem euler_pullback_power (L : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.left)
    (hsym : Nonempty ((L.pullback (GrpObj.inv (X := A)).left).sheaf ≅ L.sheaf))
    (f : AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd A) (n m : ℕ) :
    Coherent.EulerIndex.ProjectiveK.coherentEuler e ((L.pullback ((n : AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd A) - f).toMul.hom.hom.left).tensorPower m).sheaf =
      Coherent.EulerIndex.ProjectiveK.coherentEulerIndex e
        ((tensorEnd L ^ (n * n * m))
          ((tensorEnd (PullbackPowers.linearBundle A L f) ^ (n * m))
            ((tensorEnd (L.pullback f.toMul.hom.hom.left) ^ m)
              (Coherent.KTheory.Projective.coherentK0Class (Coherent.StructureDimension.ProjectiveK.coherentStructureModule A.left))))) := by
  rw [← Coherent.TensorPowers.ProjectiveK.coherentEulerIndex_tensor_power_structure]
  change Coherent.EulerIndex.ProjectiveK.coherentEulerIndex e
    ((tensorEnd (L.pullback ((n : AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd A) - f).toMul.hom.hom.left) ^ m) _) = _
  rw [tensorEnd_pullback_power A L hsym f n m]
  rfl

/-- The top coefficient in the tensor-power variable is itself polynomial
in `n`, with twice the intrinsic dimension as an upper bound. -/
theorem exists_euler_polynomials (j : Fin (r + 1)) (L : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.left)
    (hsym : Nonempty ((L.pullback (GrpObj.inv (X := A)).left).sheaf ≅ L.sheaf))
    (f : AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd A) :
    ∃ (P : ℕ → Polynomial ℚ) (D : Polynomial ℚ),
      D.natDegree ≤ 2 * AlgebraicGeometry.Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension A.hom ∧
      (∀ n : ℕ, (P n).natDegree ≤ AlgebraicGeometry.Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension A.hom) ∧
      (∀ n m : ℕ, (P n).eval (m : ℚ) =
        (Coherent.EulerIndex.ProjectiveK.coherentEuler e
          ((L.pullback ((n : AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd A) - f).toMul.hom.hom.left).tensorPower m).sheaf : ℚ)) ∧
      (∀ n : ℕ, (P n).coeff (AlgebraicGeometry.Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension A.hom) = D.eval (n : ℚ)) ∧
      D.coeff (2 * AlgebraicGeometry.Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension A.hom) =
        (Coherent.EulerIndex.ProjectiveK.coherentEulerIndex e
          (((tensorEnd L - 1) ^ AlgebraicGeometry.Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension A.hom)
            (Coherent.KTheory.Projective.coherentK0Class (Coherent.StructureDimension.ProjectiveK.coherentStructureModule A.left))) : ℚ) /
          ((AlgebraicGeometry.Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension A.hom).factorial : ℚ) := by
  have : IsIntegral A.left := GeometricallyIntegral.isIntegral_of_subsingleton A.hom
  let φ : Coherent.KTheory.Projective.CoherentK0 A.left →+ ℚ := (Int.castAddHom ℚ).comp (Coherent.EulerIndex.ProjectiveK.coherentEulerIndex e)
  let x := Coherent.KTheory.Projective.coherentK0Class (Coherent.StructureDimension.ProjectiveK.coherentStructureModule A.left)
  have hz (a b c : ℕ) (hd : AlgebraicGeometry.Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension A.hom < a + b + c) :
      ((tensorEnd L - 1) ^ a)
        (((tensorEnd (PullbackPowers.linearBundle A L f) - 1) ^ b)
          (((tensorEnd (L.pullback f.toMul.hom.hom.left) - 1) ^ c) x)) = 0 :=
    Coherent.StructureDimension.ProjectiveK.coherentTensorDifference_mixed_structure_dimension e j A.hom
      L.sheaf (PullbackPowers.linearBundle A L f).sheaf (L.pullback f.toMul.hom.hom.left).sheaf
      (AlgebraicGeometry.Quotients.FiniteDescent.LineBundleFree.Construction.LineBundleCoherence.invertible L) (AlgebraicGeometry.Quotients.FiniteDescent.LineBundleFree.Construction.LineBundleCoherence.invertible (PullbackPowers.linearBundle A L f))
      (AlgebraicGeometry.Quotients.FiniteDescent.LineBundleFree.Construction.LineBundleCoherence.invertible (L.pullback f.toMul.hom.hom.left)) a b c hd
  obtain ⟨P, D, hD, hP, hval, htop, hlead⟩ := MixedOrbitPolynomial.orbit_polynomials_with_top
    (tensorEnd L) (tensorEnd (PullbackPowers.linearBundle A L f)) (tensorEnd (L.pullback f.toMul.hom.hom.left))
    φ x (AlgebraicGeometry.Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension A.hom) hz
  refine ⟨P, D, hD, hP, ?_, htop, hlead⟩
  intro n m
  rw [hval]
  exact congrArg (fun z : ℤ => (z : ℚ)) (euler_pullback_power A e L hsym f n m).symm

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Endomorphism.EulerPolynomial
