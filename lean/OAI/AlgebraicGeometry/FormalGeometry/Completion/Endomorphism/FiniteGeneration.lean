import OAI.AlgebraicGeometry.FormalGeometry.Completion.Endomorphism.PolynomialHeight
import OAI.AlgebraicGeometry.FormalGeometry.Completion.PolynomialHeightDescent
import OAI.AlgebraicGeometry.FormalGeometry.Completion.Endomorphism.HeightDescent
import OAI.AlgebraicGeometry.FormalGeometry.Completion.Endomorphism.GeometricEmbedding

/-! # Finite Generation -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.Endomorphism.FiniteGeneration

noncomputable section

/-! The actual endomorphism group is finitely generated, and its genuine
rational endomorphism algebra is finite-dimensional. Polynomial-height
descent supplies the geometric bound; faithful base change descends it. -/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits
open scoped _root_.CategoryTheory.Obj

namespace Construction

universe u

variable {K : Type u} [Field K]
  (A : Over (Spec (CommRingCat.of K))) [GrpObj A] [IsCommMonObj A]
  [GeometricallyIntegral A.hom] [IsProper A.hom] [Smooth A.hom]

theorem algebraicEnd_finiteGenerated_of_isAlgClosed [IsAlgClosed K] : AddGroup.FG (Endomorphisms.Construction.AlgebraicEnd A) := by
  let D := HilbertDifference.Construction.endomorphismNumericalPresentation A
  let H := PolynomialHeight.Construction.endomorphismPolynomialQuadraticHeight A D
  let : Field Γ(Spec (CommRingCat.of K), ⊤) := Quotients.FiniteDescent.FieldPoint.Construction.FieldPointPrime.sectionsField K
  have : IsIntegral A.left := GeometricallyIntegral.isIntegral_of_subsingleton A.hom
  let e := Affine.ProjectiveEmbedding.Construction.projectiveAffineEmbedding A D.projective
  let d := (EffectiveHilbertDifference.Construction.lineBundleHilbertPolynomial e (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.trivial A.left) 0).natDegree - 1
  have hd : ∀ f : Endomorphisms.Construction.AlgebraicEnd A, (H.value f).natDegree ≤ d := by
    intro f
    exact PicardNumericalDegree.Construction.lineBundleHilbertDifference_natDegree_le e (D.bundle.pullback f.toMul.hom.hom.left) 0
  obtain ⟨n, hn, hnK⟩ := HeightDescent.Construction.exists_nonzero_natCast_ge_two K
  apply PolynomialQuadratic.Construction.PolynomialQuadraticHeight.finiteGenerated_of_degree_bound d H hd n hn
  intro r
  exact FiniteReduction.Construction.algebraicEnd_quotient_nsmul_finite A (n ^ r) (by
    rw [Nat.cast_pow]
    exact pow_ne_zero _ hnK)

theorem algebraicEnd_finiteGenerated : AddGroup.FG (Endomorphisms.Construction.AlgebraicEnd A) := by
  let B := Geometric.Frobenius.Construction.geometricFiberOver K A
  have : IsProper B.hom := inferInstanceAs (IsProper (pullback.snd A.hom (Geometric.Frobenius.Construction.algebraicClosureBase K)))
  have : Smooth B.hom := inferInstanceAs (Smooth (pullback.snd A.hom (Geometric.Frobenius.Construction.algebraicClosureBase K)))
  have : GeometricallyIntegral B.hom :=
    inferInstanceAs (GeometricallyIntegral (pullback.snd A.hom (Geometric.Frobenius.Construction.algebraicClosureBase K)))
  let : Ring (Endomorphisms.Construction.AlgebraicEnd (Geometric.Frobenius.Construction.geometricFiberOver K A)) := Endomorphisms.Construction.algebraicEndRing _
  let : AddMonoid (Endomorphisms.Construction.AlgebraicEnd B) := (Endomorphisms.Construction.algebraicEndRing B).toAddMonoid
  have : Module.Finite ℤ (Endomorphisms.Construction.AlgebraicEnd B) :=
    Module.Finite.iff_addGroup_fg.mpr (algebraicEnd_finiteGenerated_of_isAlgClosed B)
  let φ : Endomorphisms.Construction.AlgebraicEnd A →+* Endomorphisms.Construction.AlgebraicEnd B := GeometricEmbedding.Construction.algebraicEndGeometricBaseChange K A
  have : Module.Finite ℤ (Endomorphisms.Construction.AlgebraicEnd A) := Module.Finite.of_injective
    φ.toIntAlgHom.toLinearMap (GeometricEmbedding.Construction.algebraicEndGeometricBaseChange_injective K A)
  exact Module.Finite.iff_addGroup_fg.mp inferInstance

theorem rationalAlgebraicEnd_finiteDimensional : FiniteDimensional ℚ (Endomorphisms.Construction.RationalAlgebraicEnd A) := by
  have : Module.Finite ℤ (Endomorphisms.Construction.AlgebraicEnd A) := Module.Finite.iff_addGroup_fg.mpr (algebraicEnd_finiteGenerated A)
  infer_instance

end Construction

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.Endomorphism.FiniteGeneration
