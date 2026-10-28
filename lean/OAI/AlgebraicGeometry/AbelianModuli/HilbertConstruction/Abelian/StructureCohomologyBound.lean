import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.TwistCohomologyBound
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CanonicalGraph.FieldPolynomial

/-! # Structure Cohomology Bound -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! The actual structure sheaf of a polarized abelian scheme over an infinite field has no cohomology above its relative dimension. The graph-bundle Euler polynomial supplies the sharp degree; its coefficient is the actual positive Euler characteristic. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u
variable {K : Type u} [Field K] {g N : ℕ} {δ : Fin g → ℕ}
variable (A : PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of K)))

theorem PolarizationData.PolarizedAbelianWithFullLevel.structure_graphTwist_eulerPolynomial
    (hN : 3 ≤ N) (hNk : (N : K) ≠ 0) :
    Coherent.TwistEulerPolynomial.HasCoherentTwistEulerPolynomial A.abelian.scheme.hom
      (Line.Bundles.structureModule A.abelian.scheme.left) A.graphBundle
      (Polynomial.monomial g
        (CohomologyEulerCharacteristic.coefficientEulerCharacteristic A.abelian.scheme.hom A.graphBundle.sheaf : ℚ)) := by
  intro m
  have he := congrArg (fun z : ℤ => (z : ℚ))
    (A.graphBundle_tensorPower_euler_overField hN hNk m)
  have hunit := Proper.LineBundleEuler.coefficientEulerCharacteristic_eq_of_sheafIso A.abelian.scheme.hom
    (Tensor.ProductSheaf.tensorModuleUnitLeftIso (A.graphBundle.tensorPower m).sheaf)
  calc
    (Polynomial.monomial g
        (CohomologyEulerCharacteristic.coefficientEulerCharacteristic A.abelian.scheme.hom A.graphBundle.sheaf : ℚ)).eval (m : ℚ) =
      (CohomologyEulerCharacteristic.coefficientEulerCharacteristic A.abelian.scheme.hom (A.graphBundle.tensorPower m).sheaf : ℚ) := by
        simpa only [Polynomial.eval_monomial, Int.cast_mul, Int.cast_pow, Int.cast_natCast] using he.symm
    _ = (CohomologyEulerCharacteristic.coefficientEulerCharacteristic A.abelian.scheme.hom
        (Tensor.ProductSheaf.tensorModule (Line.Bundles.structureModule A.abelian.scheme.left) (A.graphBundle.tensorPower m).sheaf) : ℚ) :=
      congrArg (fun z : ℤ => (z : ℚ)) hunit.symm

theorem PolarizationData.PolarizedAbelianWithFullLevel.structure_cohomology_vanish_above_dimension_of_infinite [Infinite K]
    (hN : 3 ≤ N) (hNk : (N : K) ≠ 0) (q : ℕ) (hq : g < q) :
    IsZero ((Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor
      (Coefficient.ModulePresheaf.schemeCoefficientMap A.abelian.scheme.hom) q).obj (Line.Bundles.structureModule A.abelian.scheme.left)) := by
  have : (Line.Bundles.structureModule A.abelian.scheme.left).IsQuasicoherent :=
    (Line.Bundles.LineBundle.trivial A.abelian.scheme.left).isQuasicoherent
  have : (Line.Bundles.structureModule A.abelian.scheme.left).IsFiniteType :=
    (Line.Bundles.LineBundle.trivial A.abelian.scheme.left).isFiniteType
  let P := Polynomial.monomial g
    (CohomologyEulerCharacteristic.coefficientEulerCharacteristic A.abelian.scheme.hom A.graphBundle.sheaf : ℚ)
  have hdegree : P.natDegree = g := by
    apply Polynomial.natDegree_monomial_eq
    exact Int.cast_ne_zero.mpr (ne_of_gt (A.graphBundle_euler_pos_overField hN hNk))
  exact Ample.TwistCohomologyBound.coherentCohomology_vanish_above_eulerPolynomial_degree
    A.abelian.scheme.hom A.graphBundle A.graphBundle_isAmple_overField
    (Line.Bundles.structureModule A.abelian.scheme.left) P (A.structure_graphTwist_eulerPolynomial hN hNk) q
    (hdegree.symm ▸ hq)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
