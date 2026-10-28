import OAI.RepresentationTheory.Theta.Geometric.FppfPicardLocality

/-! # Homogeneous Parameter Descent -/

namespace OAI.RepresentationTheory.Theta.Geometric.HomogeneousParameterDescent

noncomputable section

/-! Homogeneity of an actual parameterized line bundle descends through
a faithfully flat, locally finitely presented parameter cover. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj

variable {S : Scheme} {g : ℕ} (A : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S) {P : Over S}
    (Q : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (P ⊗ A.scheme).left)

theorem parameterTranslationPicard_naturality {T U : Over S}
    (t : T ⟶ P) (a : T ⟶ A.scheme) (u : U ⟶ T) :
    (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardSheaf A.scheme).obj.map u.op
      ((AlgebraicGeometry.AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A.scheme).app (.op T)
        (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (A.translation a).left (ParameterizedPicardClass.parameterLineClass Q t))) =
    (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A.scheme).app (.op U)
      (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (A.translation (u ≫ a)).left (ParameterizedPicardClass.parameterLineClass Q (u ≫ t))) := by
  exact (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard_naturality A.scheme u _).trans
    (congrArg ((AlgebraicGeometry.AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A.scheme).app (.op U))
      ((A.translationClass_naturality u a (ParameterizedPicardClass.parameterLineClass Q t)).trans
        (congrArg (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (A.translation (u ≫ a)).left)
          (ParameterizedPicardClass.parameterLineClass_naturality Q t u))))

theorem homogeneous_of_fppf_parameter_pullback {P' : Over S} (p : P' ⟶ P)
    [Flat p.left] [LocallyOfFinitePresentation p.left] [Surjective p.left]
    (hQ : A.IsHomogeneousPicardClass P'
      (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (Q.pullback (p ⊗ₘ 𝟙 A.scheme).left))) :
    A.IsHomogeneousPicardClass P (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf Q) := by
  intro U f a
  obtain ⟨V, u, w, huF, huP, huS, hcomm⟩ := FppfPicardLocality.exists_fppf_test_lift p f
  let := huF
  let := huP
  let := huS
  apply FppfPicardLocality.fppfSheaf_map_injective (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardSheaf A.scheme) u
  have hpull : ParameterizedPicardClass.parameterLineClass (Q.pullback (p ⊗ₘ 𝟙 A.scheme).left) w =
      ParameterizedPicardClass.parameterLineClass Q (u ≫ f) :=
    (ParameterizedPicardClass.parameterLineClass_baseChange Q p w).symm.trans (congrArg (ParameterizedPicardClass.parameterLineClass Q) hcomm.symm)
  have H := hQ V w (u ≫ a)
  change (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A.scheme).app (.op V)
      (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (A.translation (u ≫ a)).left
        (ParameterizedPicardClass.parameterLineClass (Q.pullback (p ⊗ₘ 𝟙 A.scheme).left) w)) =
    (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A.scheme).app (.op V)
      (ParameterizedPicardClass.parameterLineClass (Q.pullback (p ⊗ₘ 𝟙 A.scheme).left) w) at H
  rw [hpull] at H
  exact (parameterTranslationPicard_naturality A Q f a u).trans
    (H.trans (ParameterizedPicardClass.parameterPicardClass_naturality Q f u).symm)

end

end OAI.RepresentationTheory.Theta.Geometric.HomogeneousParameterDescent
