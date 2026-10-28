import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Intrinsic.PolynomialAmbient

/-! # Polynomial Coordinates -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Intrinsic.PolynomialCoordinates.GradedHilbert

noncomputable section

/-! Coordinate projections and extensionality for the native relative
projective ambient scheme. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u
variable {S : Scheme.{u}} (M : Over S) {n : ℕ}

def nativePolynomialCoefficientProjection {T : Over S} (x : T ⟶ M) :
    Hilbert.Functor.ambient (PolynomialAmbient.GradedHilbert.relativeProjectiveOver M.left n) (Over.mk x.left) ⟶ Proj (Hilbert.Polynomial.GradedHilbert.grading Γ(M.left, ⊤) n) :=
  (prod.snd : (Over.mk x.left) ⨯ PolynomialAmbient.GradedHilbert.relativeProjectiveOver M.left n ⟶ PolynomialAmbient.GradedHilbert.relativeProjectiveOver M.left n).left ≫
    pullback.fst _ _

theorem nativePolynomialAmbientIso_coefficient {T : Over S} (x : T ⟶ M) :
    (PolynomialAmbient.GradedHilbert.nativePolynomialAmbientIso (n := n) M x).hom ≫ pullback.fst _ _ =
      nativePolynomialCoefficientProjection M x := by
  simp only [PolynomialAmbient.GradedHilbert.nativePolynomialAmbientIso, Iso.trans_hom, Category.assoc,
    pullbackLeftPullbackSndIso_hom_fst, pullbackSymmetry_hom_comp_fst_assoc]
  have h := Over.prodLeftIsoPullback_hom_snd (Over.mk x.left) (PolynomialAmbient.GradedHilbert.relativeProjectiveOver M.left n)
  exact (Category.assoc _ _ _).symm.trans
    (congrArg (fun f => f ≫ pullback.fst (Projective.Flatness.GradedHilbert.projectiveStructureMap (Hilbert.Polynomial.GradedHilbert.grading Γ(M.left, ⊤) n)) M.left.toSpecΓ) h)

theorem nativePolynomialAmbient_hom_ext {T : Over S} (x : T ⟶ M) {Z : Scheme.{u}}
    (f g : Z ⟶ Hilbert.Functor.ambient (PolynomialAmbient.GradedHilbert.relativeProjectiveOver M.left n) (Over.mk x.left))
    (h₁ : f ≫ Hilbert.Functor.ambientProjection (PolynomialAmbient.GradedHilbert.relativeProjectiveOver M.left n) (Over.mk x.left) =
      g ≫ Hilbert.Functor.ambientProjection (PolynomialAmbient.GradedHilbert.relativeProjectiveOver M.left n) (Over.mk x.left))
    (h₂ : f ≫ nativePolynomialCoefficientProjection M x = g ≫ nativePolynomialCoefficientProjection M x) :
    f = g := by
  apply (cancel_mono (PolynomialAmbient.GradedHilbert.nativePolynomialAmbientIso M x).hom).mp
  apply pullback.hom_ext
  · simpa only [Category.assoc, nativePolynomialAmbientIso_coefficient] using h₂
  · simpa only [Category.assoc, PolynomialAmbient.GradedHilbert.nativePolynomialAmbientIso_projection] using h₁

theorem nativePolynomialInclusion_coefficient
    (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading Γ(M.left, ⊤) n)) {T : Over S} (x : T ⟶ M) :
    PolynomialAmbient.GradedHilbert.nativePolynomialInclusion M I x ≫ nativePolynomialCoefficientProjection M x =
      pullback.fst _ _ ≫ Projective.Quotient.GradedHilbert.projectiveQuotientInclusion I := by
  rw [PolynomialAmbient.GradedHilbert.nativePolynomialInclusion, ← nativePolynomialAmbientIso_coefficient M x,
    Category.assoc, Iso.inv_hom_id_assoc, Relative.PolynomialInclusion.GradedHilbert.relativePolynomialInclusion_fst]

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Intrinsic.PolynomialCoordinates.GradedHilbert
