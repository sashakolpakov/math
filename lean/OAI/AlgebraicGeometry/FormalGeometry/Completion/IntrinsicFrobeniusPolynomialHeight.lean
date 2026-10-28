import OAI.AlgebraicGeometry.FormalGeometry.Completion.GroundNumericalPresentation
import OAI.AlgebraicGeometry.FormalGeometry.Completion.Endomorphism.HilbertSimilitude
import OAI.AlgebraicGeometry.FormalGeometry.Completion.Endomorphism.PolynomialHeight
import OAI.AlgebraicGeometry.FormalGeometry.Completion.Geometric.FrobeniusUnit
import OAI.AlgebraicGeometry.FormalGeometry.Completion.Geometric.FrobeniusLineBundle

/-! # Intrinsic Frobenius Polynomial Height -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion

noncomputable section

/-! The actual polynomial height on ground-field endomorphisms has
Frobenius-stable degree and q-scaling on every highest coefficient. -/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits
open scoped _root_.CategoryTheory.Obj TensorProduct

universe u v

def PolynomialQuadratic.Construction.PolynomialQuadraticHeight.comap {G : Type u} {H : Type v} [AddCommGroup G] [AddCommGroup H]
    (q : PolynomialQuadratic.Construction.PolynomialQuadraticHeight H) (f : G →+ H) (hf : Function.Injective f) :
    PolynomialQuadratic.Construction.PolynomialQuadraticHeight G where
  value x := q.value (f x)
  zero := by rw [map_zero, q.zero]
  detectsZero x hx := hf (by rw [q.detectsZero (f x) hx, map_zero])
  positive x hx := q.positive (f x) (fun h => hx (hf (h.trans f.map_zero.symm)))
  integer_values x := q.integer_values (f x)
  coeff_parallelogram d x y hx hy hxy := by
    simpa only [map_add, map_sub] using q.coeff_parallelogram d (f x) (f y) hx hy
      (by simpa only [map_add] using hxy)

variable (k : Type u) [Field k] [Fintype k]
  (A : Over (Spec (CommRingCat.of k))) [GrpObj A] [IsCommMonObj A]
  [Smooth A.hom] [IsProper A.hom] [GeometricallyIntegral A.hom]

attribute [local instance] Geometric.FrobeniusUnit.Construction.geometricEndRing Geometric.FrobeniusUnit.Construction.geometricEndAddCommGroup

local instance IntrinsicFrobeniusPolynomialHeight.Construction.nativeHeightGeometricProper : IsProper (Geometric.Frobenius.Construction.geometricFiberOver k A).hom :=
  inferInstanceAs (IsProper (pullback.snd A.hom (Geometric.Frobenius.Construction.algebraicClosureBase k)))

local instance IntrinsicFrobeniusPolynomialHeight.Construction.nativeHeightGeometricSmooth : Smooth (Geometric.Frobenius.Construction.geometricFiberOver k A).hom :=
  inferInstanceAs (Smooth (pullback.snd A.hom (Geometric.Frobenius.Construction.algebraicClosureBase k)))

local instance IntrinsicFrobeniusPolynomialHeight.Construction.nativeHeightGeometricIntegral : GeometricallyIntegral (Geometric.Frobenius.Construction.geometricFiberOver k A).hom :=
  inferInstanceAs (GeometricallyIntegral (pullback.snd A.hom (Geometric.Frobenius.Construction.algebraicClosureBase k)))

def IntrinsicFrobeniusPolynomialHeight.Construction.nativeEndomorphismPolynomialHeight : PolynomialQuadratic.Construction.PolynomialQuadraticHeight (Endomorphisms.Construction.AlgebraicEnd A) :=
  (Endomorphism.PolynomialHeight.Construction.endomorphismPolynomialQuadraticHeight (Geometric.Frobenius.Construction.geometricFiberOver k A) (GroundNumericalPresentation.Construction.groundGeometricNumericalPresentation k A)).comap
    (Endomorphism.GeometricEmbedding.Construction.algebraicEndGeometricBaseChange k A).toAddMonoidHom (Endomorphism.GeometricEmbedding.Construction.algebraicEndGeometricBaseChange_injective k A)

def IntrinsicFrobeniusPolynomialHeight.Construction.groundNumericalFrobeniusLineIso :
    (((GroundNumericalPresentation.Construction.groundGeometricNumericalPresentation k A).bundle).pullback
      (Endomorphism.GeometricEmbedding.Construction.algebraicEndGeometricBaseChange k A (Endomorphisms.Construction.algebraicFrobenius k A)).toMul.hom.hom.left).sheaf ≅
      ((GroundNumericalPresentation.Construction.groundGeometricNumericalPresentation k A).bundle.tensorPower (Fintype.card k)).sheaf :=
  Geometric.FrobeniusLineBundle.Construction.geometricFrobeniusLineBundleIso k A (GroundNumericalPresentation.Construction.groundGeometricAmpleBundle k A).bundle

theorem IntrinsicFrobeniusPolynomialHeight.Construction.nativeEndomorphismPolynomialHeight_frobenius_coeff
    (g : Endomorphisms.Construction.AlgebraicEnd A) (d : ℕ)
    (hd : ((IntrinsicFrobeniusPolynomialHeight.Construction.nativeEndomorphismPolynomialHeight k A).value g).natDegree ≤ d) :
    ((IntrinsicFrobeniusPolynomialHeight.Construction.nativeEndomorphismPolynomialHeight k A).value (Endomorphisms.Construction.algebraicFrobenius k A * g)).coeff d =
      (Fintype.card k : ℚ) * ((IntrinsicFrobeniusPolynomialHeight.Construction.nativeEndomorphismPolynomialHeight k A).value g).coeff d := by
  change (Endomorphism.HilbertDifference.Construction.endomorphismHilbertDifference (Geometric.Frobenius.Construction.geometricFiberOver k A) (GroundNumericalPresentation.Construction.groundGeometricNumericalPresentation k A)
    (Endomorphism.GeometricEmbedding.Construction.algebraicEndGeometricBaseChange k A (Endomorphisms.Construction.algebraicFrobenius k A * g))).coeff d = _
  rw [map_mul]
  exact Endomorphism.HilbertSimilitude.Construction.endomorphismHilbertDifference_mul_coeff (Geometric.Frobenius.Construction.geometricFiberOver k A)
    (GroundNumericalPresentation.Construction.groundGeometricNumericalPresentation k A) _ (Fintype.card k) (IntrinsicFrobeniusPolynomialHeight.Construction.groundNumericalFrobeniusLineIso k A)
    (Endomorphism.GeometricEmbedding.Construction.algebraicEndGeometricBaseChange k A g) d hd

theorem IntrinsicFrobeniusPolynomialHeight.Construction.nativeEndomorphismPolynomialHeight_frobenius_degree_le (g : Endomorphisms.Construction.AlgebraicEnd A) :
    ((IntrinsicFrobeniusPolynomialHeight.Construction.nativeEndomorphismPolynomialHeight k A).value (Endomorphisms.Construction.algebraicFrobenius k A * g)).natDegree ≤
      ((IntrinsicFrobeniusPolynomialHeight.Construction.nativeEndomorphismPolynomialHeight k A).value g).natDegree := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro d hd
  rw [IntrinsicFrobeniusPolynomialHeight.Construction.nativeEndomorphismPolynomialHeight_frobenius_coeff k A g d hd.le,
    Polynomial.coeff_eq_zero_of_natDegree_lt hd, mul_zero]

omit [Fintype k] in
theorem IntrinsicFrobeniusPolynomialHeight.Construction.nativeEndomorphismPolynomialHeight_degree_bounded :
    ∃ d : ℕ, ∀ g, ((IntrinsicFrobeniusPolynomialHeight.Construction.nativeEndomorphismPolynomialHeight k A).value g).natDegree ≤ d := by
  let B := Geometric.Frobenius.Construction.geometricFiberOver k A
  let D := GroundNumericalPresentation.Construction.groundGeometricNumericalPresentation k A
  let : Field Γ(Spec (CommRingCat.of (AlgebraicClosure k)), ⊤) := Quotients.FiniteDescent.FieldPoint.Construction.FieldPointPrime.sectionsField _
  have : IsIntegral B.left := GeometricallyIntegral.isIntegral_of_subsingleton B.hom
  let e := Affine.ProjectiveEmbedding.Construction.projectiveAffineEmbedding B D.projective
  refine ⟨(EffectiveHilbertDifference.Construction.lineBundleHilbertPolynomial e (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.trivial B.left) 0).natDegree - 1, fun g => ?_⟩
  exact PicardNumericalDegree.Construction.lineBundleHilbertDifference_natDegree_le e
    (D.bundle.pullback (Endomorphism.GeometricEmbedding.Construction.algebraicEndGeometricBaseChange k A g).toMul.hom.hom.left) 0

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion
