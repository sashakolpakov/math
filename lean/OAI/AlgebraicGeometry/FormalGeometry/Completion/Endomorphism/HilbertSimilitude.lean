import OAI.AlgebraicGeometry.FormalGeometry.Completion.LineBundlePowerHilbert
import OAI.AlgebraicGeometry.FormalGeometry.Completion.Endomorphism.HilbertDifference
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.TensorPullback

/-! # Hilbert Similitude -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.Endomorphism.HilbertSimilitude

noncomputable section

/-! A genuine pullback-power isomorphism makes every top coefficient
of the actual endomorphism Hilbert invariant scale by that power. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory

namespace Construction

universe u

variable {K : Type u} [Field K]
  (A : Over (Spec (CommRingCat.of K))) [GrpObj A] [IsCommMonObj A]

def endomorphismPullbackPowerIso (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.left) (a : Endomorphisms.Construction.AlgebraicEnd A) (n : ℕ)
    (e : (L.pullback a.toMul.hom.hom.left).sheaf ≅ (L.tensorPower n).sheaf) (g : Endomorphisms.Construction.AlgebraicEnd A) :
    (L.pullback (a * g).toMul.hom.hom.left).sheaf ≅
      ((L.pullback g.toMul.hom.hom.left).tensorPower n).sheaf :=
  ((Scheme.Modules.pullbackComp g.toMul.hom.hom.left a.toMul.hom.hom.left).app L.sheaf).symm ≪≫
    (Scheme.Modules.pullback g.toMul.hom.hom.left).mapIso e ≪≫
    Quotients.FiniteDescent.TensorPullback.Construction.TensorPullbackMap.iso g.toMul.hom.hom.left L n

variable [Infinite K] [GeometricallyIntegral A.hom]

theorem endomorphismHilbertDifference_mul_coeff (D : HilbertDifference.Construction.EndomorphismNumericalPresentation A)
    (a : Endomorphisms.Construction.AlgebraicEnd A) (n : ℕ)
    (e : (D.bundle.pullback a.toMul.hom.hom.left).sheaf ≅ (D.bundle.tensorPower n).sheaf)
    (g : Endomorphisms.Construction.AlgebraicEnd A) (d : ℕ) (hd : (HilbertDifference.Construction.endomorphismHilbertDifference A D g).natDegree ≤ d) :
    (HilbertDifference.Construction.endomorphismHilbertDifference A D (a * g)).coeff d =
      (n : ℚ) * (HilbertDifference.Construction.endomorphismHilbertDifference A D g).coeff d := by
  let : Field Γ(Spec (CommRingCat.of K), ⊤) := Quotients.FiniteDescent.FieldPoint.Construction.FieldPointPrime.sectionsField K
  have : IsIntegral A.left := GeometricallyIntegral.isIntegral_of_subsingleton A.hom
  have : Infinite Γ(Spec (CommRingCat.of K), ⊤) :=
    Infinite.of_injective (Scheme.ΓSpecIso (CommRingCat.of K)).inv
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of K)).inv).1
  let f := Affine.ProjectiveEmbedding.Construction.projectiveAffineEmbedding A D.projective
  change LineBundleHilbertCoefficients.Construction.lineBundleHilbertCoefficient f (D.bundle.pullback (a * g).toMul.hom.hom.left) 0 d = _
  rw [LineBundleHilbertCoefficients.Construction.lineBundleHilbertCoefficient_iso f _ _ (endomorphismPullbackPowerIso A D.bundle a n e g)]
  exact LineBundlePowerHilbert.Construction.lineBundleHilbertCoefficient_tensorPower f (D.bundle.pullback g.toMul.hom.hom.left)
    (D.frames.pullback g.toMul.hom.hom.left) 0 d hd n

theorem endomorphismHilbertDifference_mul_natDegree_le (D : HilbertDifference.Construction.EndomorphismNumericalPresentation A)
    (a : Endomorphisms.Construction.AlgebraicEnd A) (n : ℕ)
    (e : (D.bundle.pullback a.toMul.hom.hom.left).sheaf ≅ (D.bundle.tensorPower n).sheaf)
    (g : Endomorphisms.Construction.AlgebraicEnd A) :
    (HilbertDifference.Construction.endomorphismHilbertDifference A D (a * g)).natDegree ≤
      (HilbertDifference.Construction.endomorphismHilbertDifference A D g).natDegree := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro d hd
  rw [endomorphismHilbertDifference_mul_coeff A D a n e g d hd.le,
    Polynomial.coeff_eq_zero_of_natDegree_lt hd, mul_zero]

end Construction

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.Endomorphism.HilbertSimilitude
