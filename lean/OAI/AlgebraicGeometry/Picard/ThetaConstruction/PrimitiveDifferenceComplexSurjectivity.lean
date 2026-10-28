import OAI.AlgebraicGeometry.Picard.ThetaConstruction.SameChernDifferenceValues
import OAI.AlgebraicGeometry.Picard.ThetaConstruction.IntegralDualPointSeparation

/-! # Primitive Difference Complex Surjectivity -/

namespace OAI.AlgebraicGeometry.Picard.ThetaConstruction

noncomputable section

/-! Any original line with the primitive marked Chern pairing
represents every homogeneous complex Picard class by translation.
The parameter is obtained from the constructed native dual torus. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory

variable {g : ℕ} {E : DefinitionsIntegral.IntegralMatrix g} {T : DefinitionsIntegral.MarkedPolarizedTorus g E}
    (M : PeriodModel.Geometric.AlgebraicPeriodModel T)

theorem PeriodModel.Geometric.AlgebraicPeriodModel.primitiveDifference_complex_surjective (hE : E.transpose = -E)
    (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle M.abelian.toOver.left)
    (hL : ∀ l m : T.lattice,
      AbelianModuli.ReferenceFamily.Intrinsic.ChernPairing.nativeChernForm M.abelian L (M.nativeIntegralPeriod l) (M.nativeIntegralPeriod m) =
        (DefinitionsIntegral.Geometric.integralLatticeForm T l m : ℚ))
    (q : M.abelianScheme.homogeneousPicardSheaf.obj.obj (.op (Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase)))) :
    ∃ a : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver,
      RepresentationTheory.Theta.Geometric.ParameterizedPicardClass.parameterPicardClass (RepresentationTheory.Theta.Geometric.AbelianDifferenceBundle.abelianDifferenceBundle M.abelianScheme L) a =
        M.abelianScheme.homogeneousPicardSheafInclusion.hom.app
          (.op (Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase))) q := by
  obtain ⟨N, ⟨p⟩⟩ := IntegralDualIsogenyKernel.Geometric.exists_integralDualLatticeIsogeny M
  obtain ⟨K, Q, hQ, _, hpair, _, _, hpoints, ⟨recover⟩, _, _⟩ :=
    p.exists_normalized_complex_picard_classification hE
  obtain ⟨x, hx⟩ := hpoints.surjective q
  obtain ⟨a, ha⟩ := p.complexPoints_surjective x
  refine ⟨a, ?_⟩
  have hp : RepresentationTheory.Theta.Geometric.ParameterizedPicardClass.parameterPicardClass Q (a ≫ p.isogeny.hom) =
      RepresentationTheory.Theta.Geometric.ParameterizedPicardClass.parameterPicardClass (RepresentationTheory.Theta.Geometric.AbelianDifferenceBundle.abelianDifferenceBundle M.abelianScheme K) a :=
    congrArg ((AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard M.abelianScheme.scheme).app (.op (Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase))))
      ((RepresentationTheory.Theta.Geometric.ParameterizedPicardClass.parameterLineClass_baseChange Q p.isogeny.hom a).trans
        (RepresentationTheory.Theta.Geometric.DifferencePicardClasses.parameterLineClass_congr _ _ recover a))
  have he : a ≫ p.isogeny.hom = x := ha
  rw [he] at hp
  exact (M.sameIntegralPairing_difference_value_eq hE L K
    (fun l m => (hL l m).trans (hpair l m).symm) a).trans
      (hp.symm.trans ((RepresentationTheory.Theta.Geometric.ParameterizedHomogeneousPicard.parameterHomogeneousPicardClass_forget M.abelianScheme Q hQ x).symm.trans
        (congrArg (M.abelianScheme.homogeneousPicardSheafInclusion.hom.app
          (.op (Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase)))) hx)))

end

end OAI.AlgebraicGeometry.Picard.ThetaConstruction
