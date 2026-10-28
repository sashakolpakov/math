import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.RelativeProjective.Families
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Hilbert.ClassifierNaturality

/-! # Affine Classifier -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Affine classifiers for a relative projective Hilbert family are natural under every affine test map. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {S : Scheme.{u}} {T : Over S} {n B N : ℕ} {P : Polynomial ℚ}
variable (F : RelativeProjective.Families.RelativeProjectiveHilbertFamily T.left n P)
variable (hN : HilbertScheme.Presentations.Uniform.FamilyCoordinates.GradedHilbert.uniformHilbertFamilyDegree.{u} n P ≤ N)
variable (hflat : Truncated.FinitePersistence.truncatedFlatnessBound n N ≤ B) (htest : Truncated.PolynomialTest.truncatedHilbertTestBound n N ≤ B)
variable (hr : Generated.RankTests.GeneratedHilbertRankTest n P N)

def RelativeProjective.Families.RelativeProjectiveHilbertFamily.affineClassifyingMap {R : CommRingCat.{u}} [IsNoetherianRing R] (x : Spec R ⟶ T.left) :
    Spec R ⟶ (Truncated.GeneratedParameters.truncatedGeneratedParameters S n B (Uniform.GeneratedCoordinates.generatedHilbertRanks n P N) N).left :=
  (Flat.ClosedParameterEquivalence.flatClosedHilbertAffinePointEquiv hN hflat htest hr (x ≫ T.hom) (F.affineFamily x)).left

theorem RelativeProjective.Families.RelativeProjectiveHilbertFamily.affineClassifyingMap_over {R : CommRingCat.{u}} [IsNoetherianRing R] (x : Spec R ⟶ T.left) :
    F.affineClassifyingMap hN hflat htest hr x ≫
      (Truncated.GeneratedParameters.truncatedGeneratedParameters S n B (Uniform.GeneratedCoordinates.generatedHilbertRanks n P N) N).hom = x ≫ T.hom :=
  (Flat.ClosedParameterEquivalence.flatClosedHilbertAffinePointEquiv hN hflat htest hr (x ≫ T.hom) (F.affineFamily x)).w

theorem RelativeProjective.Families.RelativeProjectiveHilbertFamily.affineClassifyingMap_coefficients {R A : CommRingCat.{u}}
    [IsNoetherianRing R] [IsNoetherianRing A] (x : Spec R ⟶ T.left) (φ : R ⟶ A) :
    Spec.map φ ≫ F.affineClassifyingMap hN hflat htest hr x =
      F.affineClassifyingMap hN hflat htest hr (Spec.map φ ≫ x) := by
  have he : F.affineFamily (Spec.map φ ≫ x) =
      (F.affineFamily x).coefficientBaseChange hN hflat htest hr φ :=
    Subtype.ext (F.family.affineProjectivePullback_coefficient x φ)
  have h := congrArg Over.Hom.left (Hilbert.ClassifierNaturality.flatClosedHilbertClassifier_coefficientBaseChange
    hN hflat htest hr (x ≫ T.hom) (F.affineFamily x) φ)
  rw [← he] at h
  simp only [Over.comp_left, Over.homMk_left] at h
  unfold RelativeProjective.Families.RelativeProjectiveHilbertFamily.affineClassifyingMap
  rw [Category.assoc]
  exact h.symm

theorem RelativeProjective.Families.RelativeProjectiveHilbertFamily.affineClassifyingMap_natural {R A : CommRingCat.{u}}
    [IsNoetherianRing R] [IsNoetherianRing A] (x : Spec R ⟶ T.left) (a : Spec A ⟶ Spec R) :
    a ≫ F.affineClassifyingMap hN hflat htest hr x = F.affineClassifyingMap hN hflat htest hr (a ≫ x) := by
  let φ : R ⟶ A := (Spec.fullyFaithful.preimage a).unop
  have he : Spec.map φ = a := Spec.fullyFaithful.map_preimage a
  rw [← he]
  exact F.affineClassifyingMap_coefficients hN hflat htest hr x φ

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
