import OAI.NumberTheory.PadicHodge.IntegralComparison.Coherent.TensorPowers
import OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.EulerSections
import OAI.AlgebraicGeometry.SheafCohomology.Projective.UniversalPowers
import OAI.AlgebraicGeometry.FormalGeometry.Completion.PolynomialDifference

/-! # Euler Hilbert -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Coherent.EulerHilbert.ProjectiveK

noncomputable section

/-! The actual coherent Euler index is the constant term of the Hilbert
polynomial. The proof uses tensor nilpotence and Serre vanishing, and
works over an arbitrary infinite field. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry MonoidalCategory

open OAI.AlgebraicGeometry.FormalGeometry.Completion.PolynomialDifference.Construction OAI.AlgebraicGeometry.SheafCohomology.Projective.UniversalPowers.Dimension

universe u
attribute [local instance] MvPolynomial.gradedAlgebra OAI.AlgebraicGeometry.SheafCohomology.Projective.Monoidal.Scheme.Modules.monoidalCategory

variable {K : Type u} [Field K] [Infinite K] {r : ℕ} {A : Scheme.{u}} [IsIntegral A]
  (f : A ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) K))
  [IsClosedImmersion f] (j : Fin (r + 1))

def projectiveLineBundle : OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A :=
  (OAI.AlgebraicGeometry.Quotients.FiniteDescent.ProjectiveCoordinatesApp.Construction.ProjectiveCoordinates.bundle (R := K) j).pullback f

omit [Infinite K] [AlgebraicGeometry.IsIntegral A] in
theorem coherentEulerIndex_hyperplane_orbit (M : KTheory.Projective.CoherentModule A) (n : ℕ) :
    EulerIndex.ProjectiveK.coherentEulerIndex f
      ((KTheory.Projective.coherentTensorEnd (projectiveLineBundle f j).sheaf
        (OAI.AlgebraicGeometry.Quotients.FiniteDescent.LineBundleFree.Construction.LineBundleCoherence.invertible (projectiveLineBundle f j)) ^ n)
          (KTheory.Projective.coherentK0Class M)) =
      EulerIndex.ProjectiveK.coherentEuler f (OAI.AlgebraicGeometry.FormalGeometry.Completion.ClosedHilbertNumerics.Construction.closedProjectiveTwist f M.sheaf j n) := by
  rw [TensorPowers.ProjectiveK.coherentTensorEnd_power]
  change EulerIndex.ProjectiveK.coherentEulerIndex f
    (KTheory.Projective.coherentTensorK0 ((projectiveLineBundle f j).tensorPower n).sheaf _
      (KTheory.Projective.coherentK0Class M)) = _
  rw [EulerIndex.ProjectiveK.coherentEulerIndex_tensor_class]
  let e := OAI.AlgebraicGeometry.SheafCohomology.Projective.UniversalPowers.Dimension.pullbackProjectiveTwistUniversalIso f j (projectiveLineBundle f j) (Iso.refl _) n
  exact EulerIndex.ProjectiveK.coherentEuler_eq_of_iso f (Iso.refl M.sheaf ⊗ᵢ e.symm)

theorem coherentHilbertPolynomial_eval_eq_euler_orbit (M : KTheory.Projective.CoherentModule A) (n : ℕ) :
    (HilbertFiltration.ProjectiveK.coherentHilbertPolynomial f j M).eval (n : ℚ) =
      (EulerIndex.ProjectiveK.coherentEulerIndex f
        ((KTheory.Projective.coherentTensorEnd (projectiveLineBundle f j).sheaf
          (OAI.AlgebraicGeometry.Quotients.FiniteDescent.LineBundleFree.Construction.LineBundleCoherence.invertible (projectiveLineBundle f j)) ^ n)
            (KTheory.Projective.coherentK0Class M)) : ℚ) := by
  let T := KTheory.Projective.coherentTensorEnd (projectiveLineBundle f j).sheaf
    (OAI.AlgebraicGeometry.Quotients.FiniteDescent.LineBundleFree.Construction.LineBundleCoherence.invertible (projectiveLineBundle f j))
  let x := KTheory.Projective.coherentK0Class M
  let d := (HilbertFiltration.ProjectiveK.coherentHilbertPolynomial f j M).natDegree + 1
  have hx : x ∈ HilbertFiltration.ProjectiveK.coherentHilbertFiltration f j d := by
    apply HilbertFiltration.ProjectiveK.coherentK0Class_mem_hilbertFiltration
    exact Polynomial.degree_le_natDegree.trans_lt
      (WithBot.coe_lt_coe.mpr (Nat.lt_succ_self _))
  have hT : ((T - 1) ^ d) x = 0 :=
    TensorNilpotence.ProjectiveK.coherentTensorDifference_pow_eq_zero_of_hilbertFiltration f j
      (projectiveLineBundle f j).sheaf
      (OAI.AlgebraicGeometry.Quotients.FiniteDescent.LineBundleFree.Construction.LineBundleCoherence.invertible (projectiveLineBundle f j)) d x hx
  let P := OAI.AlgebraicGeometry.SheafCohomology.Projective.EndomorphismOrbitPolynomial.endomorphismOrbitPolynomial T (EulerIndex.ProjectiveK.coherentEulerIndex f) x d
  have hP (m : ℕ) : P.eval (m : ℚ) =
      (EulerIndex.ProjectiveK.coherentEuler f (OAI.AlgebraicGeometry.FormalGeometry.Completion.ClosedHilbertNumerics.Construction.closedProjectiveTwist f M.sheaf j m) : ℚ) := by
    rw [OAI.AlgebraicGeometry.SheafCohomology.Projective.EndomorphismOrbitPolynomial.endomorphismOrbitPolynomial_eval_of_apply_eq_zero T (EulerIndex.ProjectiveK.coherentEulerIndex f) x d hT]
    exact congrArg (fun z : ℤ => (z : ℚ)) (coherentEulerIndex_hyperplane_orbit f j M m)
  have he : P = HilbertFiltration.ProjectiveK.coherentHilbertPolynomial f j M := by
    obtain ⟨b, hb⟩ := Projective.EulerSections.K.projectiveEuler_eventually_sections
      (OAI.AlgebraicGeometry.FormalGeometry.Completion.ClosedHilbertNumerics.Construction.coherentClosedDirectImage f M.sheaf) j
    obtain ⟨c, hc⟩ := OAI.AlgebraicGeometry.FormalGeometry.Completion.Projective.Numerics.Construction.projectiveHilbertPolynomial_spec
      (OAI.AlgebraicGeometry.FormalGeometry.Completion.ClosedHilbertNumerics.Construction.coherentClosedDirectImage f M.sheaf) j
    apply OAI.AlgebraicGeometry.FormalGeometry.Completion.EventualPolynomial.Construction.polynomial_eq_of_eventual_nat_eval _ _ (max b c)
    intro m hm
    rw [hP]
    let e := (OAI.AlgebraicGeometry.SheafCohomology.Projective.TwistProjectionFormula.MvPolynomial.coordinateHyperplanePoleSheafPowerPushforwardTensorIso f j m).app M.sheaf
    calc
      (EulerIndex.ProjectiveK.coherentEuler f (OAI.AlgebraicGeometry.FormalGeometry.Completion.ClosedHilbertNumerics.Construction.closedProjectiveTwist f M.sheaf j m) : ℚ) =
          (OAI.AlgebraicGeometry.SheafCohomology.Projective.Euler.MvPolynomial.projectiveSheafEuler
            (OAI.AlgebraicGeometry.FormalGeometry.Completion.ClosedHilbertNumerics.Construction.coherentClosedDirectImage f M.sheaf ⊗
              OAI.AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := K) j m) : ℚ) :=
        congrArg (fun z : ℤ => (z : ℚ)) (OAI.AlgebraicGeometry.SheafCohomology.Projective.Euler.MvPolynomial.projectiveSheafEuler_eq_of_iso e.symm)
      _ = OAI.AlgebraicGeometry.FormalGeometry.Completion.Projective.Numerics.Construction.projectiveHilbertFunction (OAI.AlgebraicGeometry.FormalGeometry.Completion.ClosedHilbertNumerics.Construction.coherentClosedDirectImage f M.sheaf) j m :=
        hb m ((le_max_left _ _).trans hm)
      _ = (HilbertFiltration.ProjectiveK.coherentHilbertPolynomial f j M).eval (m : ℚ) :=
        hc m ((le_max_right _ _).trans hm)
  rw [← he]
  exact OAI.AlgebraicGeometry.SheafCohomology.Projective.EndomorphismOrbitPolynomial.endomorphismOrbitPolynomial_eval_of_apply_eq_zero T (EulerIndex.ProjectiveK.coherentEulerIndex f) x d hT n

theorem coherentEuler_eq_hilbert_at_zero (M : KTheory.Projective.CoherentModule A) :
    (EulerIndex.ProjectiveK.coherentEuler f M.sheaf : ℚ) = (HilbertFiltration.ProjectiveK.coherentHilbertPolynomial f j M).eval 0 := by
  simpa only [Nat.cast_zero, pow_zero, AddMonoid.End.one_apply,
    EulerIndex.ProjectiveK.coherentEulerIndex_class] using
      (coherentHilbertPolynomial_eval_eq_euler_orbit f j M 0).symm

theorem coherentProjectiveTwist_euler (M : KTheory.Projective.CoherentModule A) (n : ℕ) :
    (EulerIndex.ProjectiveK.coherentEuler f (OAI.AlgebraicGeometry.FormalGeometry.Completion.ClosedHilbertNumerics.Construction.closedProjectiveTwist f M.sheaf j n) : ℚ) =
      (HilbertFiltration.ProjectiveK.coherentHilbertPolynomial f j M).eval (n : ℚ) := by
  rw [coherentHilbertPolynomial_eval_eq_euler_orbit, coherentEulerIndex_hyperplane_orbit]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Coherent.EulerHilbert.ProjectiveK
