import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SheafOpenCoverDetection
import OAI.RepresentationTheory.Theta.Geometric.ParameterizedHomogeneousPicard

/-! # Line Open Locality -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Homogeneous.LineOpenLocality

noncomputable section

/-! Homogeneity of an actual parameterized line bundle is local on an
open cover of its parameter scheme. No local triviality or reducedness
of the test scheme is required. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open OAI.RepresentationTheory.Theta.Geometric.ParameterizedHomogeneousPicard

universe u
variable {S : Scheme.{u}} {g : ℕ} (A : Abelian.Schemes.AbelianScheme g S) {P : Over S}
  (Q : Line.Bundles.LineBundle (P ⊗ A.scheme).left) (C : P.left.OpenCover.{u})

/-- Invariance under translation can be tested on the genuine
pullback of the parameter cover to each test scheme. -/
theorem homogeneous_of_parameter_openCover
    (hQ : ∀ i, A.IsHomogeneousPicardClass (Embedded.FamilyOpenCover.overOpenCoverObject P C i)
      (Line.Bundles.LineBundle.classOf (Q.pullback (Embedded.FamilyOpenCover.overOpenCoverMap P C i ▷ A.scheme).left))) :
    A.IsHomogeneousPicardClass P (Line.Bundles.LineBundle.classOf Q) := by
  intro T f a
  let V := C.pullback₁ f.left
  apply SheafOpenCoverDetection.fppfSheaf_eq_of_openCover (Picard.PicardSheaf.relativePicardSheaf A.scheme) T V
  intro i
  let U := Embedded.FamilyOpenCover.overOpenCoverObject T V i
  let t : U ⟶ T := Embedded.FamilyOpenCover.overOpenCoverMap T V i
  let W := Embedded.FamilyOpenCover.overOpenCoverObject P C i
  let j : W ⟶ P := Embedded.FamilyOpenCover.overOpenCoverMap P C i
  let w : U ⟶ W := Over.homMk (pullback.snd f.left (C.f i)) (by
    change pullback.snd f.left (C.f i) ≫ (C.f i ≫ P.hom) =
      pullback.fst f.left (C.f i) ≫ T.hom
    rw [← Category.assoc, ← pullback.condition, Category.assoc, f.w])
  have hw : t ≫ f = w ≫ j := by
    apply Over.OverMorphism.ext
    exact pullback.condition
  have hi : A.IsHomogeneousPicardClass W
      (Line.Bundles.LineBundle.classOf (Q.pullback (j ⊗ₘ 𝟙 A.scheme).left)) := by
    simpa only [tensorHom_id] using hQ i
  have hpull : RepresentationTheory.Theta.Geometric.ParameterizedPicardClass.parameterLineClass (Q.pullback (j ⊗ₘ 𝟙 A.scheme).left) w =
      RepresentationTheory.Theta.Geometric.ParameterizedPicardClass.parameterLineClass Q (t ≫ f) :=
    (RepresentationTheory.Theta.Geometric.ParameterizedPicardClass.parameterLineClass_baseChange Q j w).symm.trans
      (congrArg (RepresentationTheory.Theta.Geometric.ParameterizedPicardClass.parameterLineClass Q) hw.symm)
  have H := hi U w (t ≫ a)
  change (Picard.PicardSheaf.toRelativePicard A.scheme).app (.op U)
      (Line.Bundles.LineBundle.pullbackClass (A.translation (t ≫ a)).left
        (RepresentationTheory.Theta.Geometric.ParameterizedPicardClass.parameterLineClass (Q.pullback (j ⊗ₘ 𝟙 A.scheme).left) w)) =
    (Picard.PicardSheaf.toRelativePicard A.scheme).app (.op U)
      (RepresentationTheory.Theta.Geometric.ParameterizedPicardClass.parameterLineClass (Q.pullback (j ⊗ₘ 𝟙 A.scheme).left) w) at H
  rw [hpull] at H
  exact (RepresentationTheory.Theta.Geometric.HomogeneousParameterDescent.parameterTranslationPicard_naturality A Q f a t).trans
    (H.trans (RepresentationTheory.Theta.Geometric.ParameterizedPicardClass.parameterPicardClass_naturality Q f t).symm)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Homogeneous.LineOpenLocality
