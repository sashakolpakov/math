import OAI.AlgebraicGeometry.Picard.ThetaConstruction.ComplexBijection
import OAI.AlgebraicGeometry.Picard.ThetaConstruction.DualInjectivity
import OAI.RepresentationTheory.Theta.Geometric.ArbitraryTestPicardInjectivity
import OAI.RepresentationTheory.Theta.Geometric.ParameterizedHomogeneousPicard

/-! # Complex Picard Construction -/

namespace OAI.AlgebraicGeometry.Picard.ThetaConstruction

noncomputable section

/-! The primitive ThetaConstruction theta construction supplies a normalized
homogeneous family separating all actual test schemes and classifying
the actual homogeneous Picard sheaf at Spec C. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

variable {dim : ℕ} {E : DefinitionsIntegral.IntegralMatrix dim} {T : DefinitionsIntegral.MarkedPolarizedTorus dim E}
    {M : PeriodModel.Geometric.AlgebraicPeriodModel T} {N : IntegralDualModel.Geometric.IntegralDualAlgebraicModel T}

theorem IntegralDualIsogenyKernel.Geometric.IntegralDualLatticeIsogeny.homogeneousParameterMap_mono
    (Q : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (N.abelianScheme.scheme ⊗ M.abelianScheme.scheme).left)
    (hQ : M.abelianScheme.IsHomogeneousPicardClass N.abelianScheme.scheme (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf Q))
    (hinj : ∀ U : Over Foundations.Scheme.ProjectiveSpace.complexBase,
      Function.Injective (fun t : U ⟶ N.abelianScheme.scheme => RepresentationTheory.Theta.Geometric.ParameterizedPicardClass.parameterPicardClass Q t)) :
    Mono (RepresentationTheory.Theta.Geometric.ParameterizedHomogeneousPicard.homogeneousParameterMap M.abelianScheme Q hQ) := by
  have hcomponent (U : (Over Foundations.Scheme.ProjectiveSpace.complexBase)ᵒᵖ) : Mono ((RepresentationTheory.Theta.Geometric.ParameterizedHomogeneousPicard.homogeneousParameterMap M.abelianScheme Q hQ).app U) := by
    apply ConcreteCategory.mono_of_injective
    intro a b h
    apply ULift.ext
    apply hinj U.unop
    exact (RepresentationTheory.Theta.Geometric.ParameterizedHomogeneousPicard.parameterHomogeneousPicardClass_forget M.abelianScheme Q hQ a.down).symm.trans
      ((congrArg (M.abelianScheme.homogeneousPicardSheafInclusion.hom.app U) h).trans
        (RepresentationTheory.Theta.Geometric.ParameterizedHomogeneousPicard.parameterHomogeneousPicardClass_forget M.abelianScheme Q hQ b.down))
  exact NatTrans.mono_of_mono_app (RepresentationTheory.Theta.Geometric.ParameterizedHomogeneousPicard.homogeneousParameterMap M.abelianScheme Q hQ)

theorem IntegralDualIsogenyKernel.Geometric.IntegralDualLatticeIsogeny.exists_normalized_complex_picard_classification
    (p : IntegralDualIsogenyKernel.Geometric.IntegralDualLatticeIsogeny M N) (hE : E.transpose = -E) :
    ∃ (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle M.abelianScheme.scheme.left)
      (Q : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (N.abelianScheme.scheme ⊗ M.abelianScheme.scheme).left)
      (hQ : M.abelianScheme.IsHomogeneousPicardClass N.abelianScheme.scheme (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf Q)),
      L.IsAmple ∧
      (∀ l m : T.lattice, AbelianModuli.ReferenceFamily.Intrinsic.ChernPairing.nativeChernForm M.abelian L
        (M.nativeIntegralPeriod l) (M.nativeIntegralPeriod m) = (DefinitionsIntegral.Geometric.integralLatticeForm T l m : ℚ)) ∧
      Mono (RepresentationTheory.Theta.Geometric.ParameterizedHomogeneousPicard.homogeneousParameterMap M.abelianScheme Q hQ) ∧
      (∀ U : Over Foundations.Scheme.ProjectiveSpace.complexBase,
        Function.Injective (fun t : U ⟶ N.abelianScheme.scheme => RepresentationTheory.Theta.Geometric.ParameterizedPicardClass.parameterPicardClass Q t)) ∧
      Function.Bijective (fun x : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints N.abelian.toOver =>
        RepresentationTheory.Theta.Geometric.ParameterizedHomogeneousPicard.parameterHomogeneousPicardClass M.abelianScheme Q hQ x) ∧
      Nonempty ((Q.pullback (p.isogeny.hom ⊗ₘ 𝟙 M.abelianScheme.scheme).left).sheaf ≅
        (RepresentationTheory.Theta.Geometric.AbelianDifferenceBundle.abelianDifferenceBundle M.abelianScheme L).sheaf) ∧
      Nonempty ((Q.pullback (lift (1 : M.abelianScheme.scheme ⟶ N.abelianScheme.scheme)
        (𝟙 M.abelianScheme.scheme)).left).sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule M.abelianScheme.scheme.left) ∧
      Nonempty ((Q.pullback (lift (𝟙 N.abelianScheme.scheme)
        (1 : N.abelianScheme.scheme ⟶ M.abelianScheme.scheme)).left).sheaf ≅
          AbelianModuli.HilbertConstruction.Line.Bundles.structureModule N.abelianScheme.scheme.left) := by
  let : IsProper N.abelianScheme.scheme.hom := N.abelian.variety.presentation.projective.isProper
  let : Smooth N.abelianScheme.scheme.hom := N.abelian.variety.presentation.smooth
  obtain ⟨U, V, jU, jV, Q, _hpos, hdeg, _hjU, _hjV, heU, heV, hamp, hcube, hpair,
    hhom, ⟨recover⟩, ⟨eN⟩, ⟨eM⟩⟩ := p.exists_normalized_homogeneous_primitive_difference hE
  have hcomplex := RepresentationTheory.Theta.Geometric.PointPicardClassInjectivity.parameterPicardClass_complex_injective M.abelianScheme Q eM
    (p.pointBundleClass_injective hE U V hdeg jU jV heU heV hcube Q recover)
  have hdual := p.parameterPicardClass_dual_injective U V hdeg jU jV heU heV hcube Q recover eM eN
  have hinj (W : Over Foundations.Scheme.ProjectiveSpace.complexBase) :
      Function.Injective (fun t : W ⟶ N.abelianScheme.scheme => RepresentationTheory.Theta.Geometric.ParameterizedPicardClass.parameterPicardClass Q t) :=
    RepresentationTheory.Theta.Geometric.ArbitraryTestPicardInjectivity.parameterPicardClass_arbitraryTest_injective M.abelianScheme Q eM hdual hcomplex W
      (p.parameterPicardHom (RepresentationTheory.Theta.Geometric.AlgebraicQuotient.algebraicThetaQuotient jU.left jV.left) hcube Q recover W) (fun _ => rfl)
  exact ⟨RepresentationTheory.Theta.Geometric.AlgebraicQuotient.algebraicThetaQuotient jU.left jV.left, Q, hhom, hamp, hpair,
    IntegralDualIsogenyKernel.Geometric.IntegralDualLatticeIsogeny.homogeneousParameterMap_mono Q hhom hinj, hinj,
    p.nativeHomogeneousPointPicardClass_bijective U V hdeg jU jV heU heV Q recover hhom,
    ⟨recover⟩, ⟨eN⟩, ⟨eM⟩⟩

end

end OAI.AlgebraicGeometry.Picard.ThetaConstruction
