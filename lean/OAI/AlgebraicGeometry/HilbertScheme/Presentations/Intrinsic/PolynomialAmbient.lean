import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Relative.PolynomialInclusion
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Hilbert.Functor

/-! # Polynomial Ambient -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Intrinsic.PolynomialAmbient.GradedHilbert

noncomputable section

/-! The relative polynomial ambient scheme is canonically the actual
fiber-product ambient used by the native Hilbert functor. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

abbrev relativeProjectiveOver (M : Scheme.{u}) (n : ℕ) : Over M :=
  Over.mk (pullback.snd (Projective.Flatness.GradedHilbert.projectiveStructureMap (Hilbert.Polynomial.GradedHilbert.grading Γ(M, ⊤) n)) M.toSpecΓ)

variable {S : Scheme.{u}} (M : Over S) {n : ℕ}

def nativePolynomialAmbientIso {T : Over S} (x : T ⟶ M) :
    Hilbert.Functor.ambient (relativeProjectiveOver M.left n) (Over.mk x.left) ≅
      Relative.PolynomialInclusion.GradedHilbert.relativePolynomialAmbient (n := n) M x :=
  Over.prodLeftIsoPullback (Over.mk x.left) (relativeProjectiveOver M.left n) ≪≫
    pullbackSymmetry x.left (pullback.snd (Projective.Flatness.GradedHilbert.projectiveStructureMap (Hilbert.Polynomial.GradedHilbert.grading Γ(M.left, ⊤) n)) M.left.toSpecΓ) ≪≫
      pullbackLeftPullbackSndIso (Projective.Flatness.GradedHilbert.projectiveStructureMap (Hilbert.Polynomial.GradedHilbert.grading Γ(M.left, ⊤) n)) M.left.toSpecΓ x.left

theorem nativePolynomialAmbientIso_projection {T : Over S} (x : T ⟶ M) :
    (nativePolynomialAmbientIso (n := n) M x).hom ≫ pullback.snd _ _ =
      Hilbert.Functor.ambientProjection (relativeProjectiveOver M.left n) (Over.mk x.left) := by
  simp only [nativePolynomialAmbientIso, Iso.trans_hom, Category.assoc,
    pullbackLeftPullbackSndIso_hom_snd, pullbackSymmetry_hom_comp_snd]
  exact Over.prodLeftIsoPullback_hom_fst (Over.mk x.left) (relativeProjectiveOver M.left n)

theorem nativePolynomialAmbientIso_inv_projection {T : Over S} (x : T ⟶ M) :
    (nativePolynomialAmbientIso (n := n) M x).inv ≫
      Hilbert.Functor.ambientProjection (relativeProjectiveOver M.left n) (Over.mk x.left) =
        pullback.snd _ _ := by
  rw [← nativePolynomialAmbientIso_projection M x, Iso.inv_hom_id_assoc]

variable (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading Γ(M.left, ⊤) n))

def nativePolynomialInclusion {T : Over S} (x : T ⟶ M) : Relative.PolynomialFamily.GradedHilbert.relativePolynomialFamily M I x ⟶
    Hilbert.Functor.ambient (relativeProjectiveOver M.left n) (Over.mk x.left) :=
  Relative.PolynomialInclusion.GradedHilbert.relativePolynomialInclusion M I x ≫ (nativePolynomialAmbientIso M x).inv

instance nativePolynomialInclusion_isClosedImmersion {T : Over S} (x : T ⟶ M) :
    IsClosedImmersion (nativePolynomialInclusion M I x) :=
  inferInstanceAs (IsClosedImmersion (Relative.PolynomialInclusion.GradedHilbert.relativePolynomialInclusion M I x ≫ (nativePolynomialAmbientIso M x).inv))

theorem nativePolynomialInclusion_projection {T : Over S} (x : T ⟶ M) :
    nativePolynomialInclusion M I x ≫
      Hilbert.Functor.ambientProjection (relativeProjectiveOver M.left n) (Over.mk x.left) =
        Relative.PolynomialFamily.GradedHilbert.relativePolynomialProjection M I x := by
  rw [nativePolynomialInclusion, Category.assoc, nativePolynomialAmbientIso_inv_projection,
    Relative.PolynomialInclusion.GradedHilbert.relativePolynomialInclusion_projection]

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Intrinsic.PolynomialAmbient.GradedHilbert
