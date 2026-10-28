import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Smooth.RelativeAffinePoint
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Generated.EmbeddedBaseChange

/-! # Relative Affine Naturality -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! The affine parameter points of a smooth relative Hilbert family are natural for every affine test map. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {S : Scheme.{u}} {T : Over S} {n B N : ℕ} {P : Polynomial ℚ}
variable (F : RelativeProjective.Families.RelativeProjectiveHilbertFamily T.left n P) [Smooth F.family.scheme.hom]
variable (hN : HilbertScheme.Presentations.Uniform.FamilyCoordinates.GradedHilbert.uniformHilbertFamilyDegree.{u} n P ≤ N) (hflat : Truncated.FinitePersistence.truncatedFlatnessBound n N ≤ B)

theorem RelativeProjective.Families.RelativeProjectiveHilbertFamily.smoothAffinePoint_coefficients {R A : CommRingCat.{u}} (x : Spec R ⟶ T.left) (φ : R ⟶ A) :
    Spec.map φ ≫ (F.smoothAffinePoint hN hflat x).left =
      (F.smoothAffinePoint hN hflat (Spec.map φ ≫ x)).left := by
  let a : Over.mk ((Spec.map φ ≫ x) ≫ T.hom) ⟶
      Truncated.GeneratedParameters.truncatedGeneratedParameters S n B (Uniform.GeneratedCoordinates.generatedHilbertRanks n P N) N :=
    Over.homMk (Spec.map φ ≫ (F.smoothAffinePoint hN hflat x).left) (by
      exact (Category.assoc _ _ _).trans
        ((congrArg (fun k : Spec R ⟶ S => Spec.map φ ≫ k) (F.smoothAffinePoint hN hflat x).w).trans
          (Category.assoc _ _ _).symm))
  have : Smooth (F.affineFamily (Spec.map φ ≫ x)).val.scheme.hom := F.affineFamily_smooth _
  have ha : Generated.PullbackAffineCharts.generatedPullbackFamilyAtAffinePoint a.left hflat = (F.affineFamily (Spec.map φ ≫ x)).val := by
    change Generated.PullbackAffineCharts.generatedPullbackFamilyAtAffinePoint (Spec.map φ ≫ (F.smoothAffinePoint hN hflat x).left) hflat = _
    rw [Generated.EmbeddedBaseChange.generatedPullbackFamilyAtAffinePoint_baseChange, F.smoothAffinePoint_pullback hN hflat x]
    exact (F.family.affineProjectivePullback_coefficient x φ).symm
  exact congrArg Over.Hom.left (SmoothHilbert.AffineUniqueness.smoothHilbertAffinePoint_unique
    (F.affineFamily (Spec.map φ ≫ x)) hN hflat ((Spec.map φ ≫ x) ≫ T.hom)
    a (F.smoothAffinePoint hN hflat (Spec.map φ ≫ x)) ha (F.smoothAffinePoint_pullback hN hflat _))

theorem RelativeProjective.Families.RelativeProjectiveHilbertFamily.smoothAffinePoint_natural {R A : CommRingCat.{u}} (x : Spec R ⟶ T.left) (a : Spec A ⟶ Spec R) :
    a ≫ (F.smoothAffinePoint hN hflat x).left = (F.smoothAffinePoint hN hflat (a ≫ x)).left := by
  let φ : R ⟶ A := (Spec.fullyFaithful.preimage a).unop
  have he : Spec.map φ = a := Spec.fullyFaithful.map_preimage a
  rw [← he]
  exact F.smoothAffinePoint_coefficients hN hflat x φ

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
