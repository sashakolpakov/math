import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.ComplexPicardBijection
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.PicardMonomorphism

/-! # Complex Picard Construction -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference

noncomputable section

/-! The actual theta construction produces one normalized ample
family whose Picard parameter map is a monomorphism on all test schemes
and a bijection on complex points. Relative surjectivity is not assumed. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E]
    [NumberField.IsCMField E] {s : ℕ} {P : Datum.RankThreePELDatum E s}
    {z : P.domain} {F : Fiber.ReferenceAnalyticFiber P z} {hP : P.IsAdmissible}
    {M : AlgebraicModel.ReferenceAlgebraicModel F hP} {D : DualModel.ReferenceDualModel F hP}
    (p : IsogenyKernel.ReferenceLatticeIsogeny M D)

local instance IsogenyKernel.ReferenceLatticeIsogeny.complexPicardConstruction_proper : IsProper D.abelianScheme.scheme.hom :=
  D.abelian.variety.presentation.projective.isProper
local instance IsogenyKernel.ReferenceLatticeIsogeny.complexPicardConstruction_finiteType : LocallyOfFiniteType D.abelianScheme.scheme.hom := by
  let : Smooth D.abelianScheme.scheme.hom := D.abelian.variety.presentation.smooth
  infer_instance

include p in
theorem IsogenyKernel.ReferenceLatticeIsogeny.exists_normalized_complex_picard_classification :
    ∃ (L : HilbertConstruction.Line.Bundles.LineBundle M.abelianScheme.scheme.left)
      (Q : HilbertConstruction.Line.Bundles.LineBundle (D.abelianScheme.scheme ⊗ M.abelianScheme.scheme).left)
      (hQ : M.abelianScheme.IsHomogeneousPicardClass D.abelianScheme.scheme (HilbertConstruction.Line.Bundles.LineBundle.classOf Q)),
      L.IsAmple ∧
      (∀ u v : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E, Intrinsic.ChernPairing.nativeChernForm M.abelian L
        (M.nativeReferenceMarking u) (M.nativeReferenceMarking v) = P.traceForm u v) ∧
      Mono (RepresentationTheory.Theta.Geometric.ParameterizedHomogeneousPicard.homogeneousParameterMap M.abelianScheme Q hQ) ∧
      Function.Bijective (fun x : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints D.abelian.toOver =>
        RepresentationTheory.Theta.Geometric.ParameterizedHomogeneousPicard.parameterHomogeneousPicardClass M.abelianScheme Q hQ x) ∧
      (∀ T : Over Foundations.Scheme.ProjectiveSpace.complexBase, RepresentationTheory.Theta.Geometric.ParameterizedHomogeneousPicard.parameterHomogeneousPicardClass M.abelianScheme Q hQ
        (1 : T ⟶ D.abelianScheme.scheme) = M.abelianScheme.trivialHomogeneousPicardClass T) ∧
      Nonempty ((Q.pullback (p.isogeny.hom ⊗ₘ 𝟙 M.abelianScheme.scheme).left).sheaf ≅
        (RepresentationTheory.Theta.Geometric.AbelianDifferenceBundle.abelianDifferenceBundle M.abelianScheme L).sheaf) ∧
      Nonempty ((Q.pullback (lift (1 : M.abelianScheme.scheme ⟶ D.abelianScheme.scheme)
        (𝟙 M.abelianScheme.scheme)).left).sheaf ≅ HilbertConstruction.Line.Bundles.structureModule M.abelianScheme.scheme.left) ∧
      Nonempty ((Q.pullback (lift (𝟙 D.abelianScheme.scheme)
        (1 : D.abelianScheme.scheme ⟶ M.abelianScheme.scheme)).left).sheaf ≅
          HilbertConstruction.Line.Bundles.structureModule D.abelianScheme.scheme.left) := by
  obtain ⟨U, V, jU, jV, Q, _, hdeg, _, _, heU, heV, hamp, hcube, hhom, ⟨recover⟩, ⟨eD⟩, ⟨eA⟩⟩ :=
    p.exists_normalized_homogeneous_theta_difference
  have hcomplex := RepresentationTheory.Theta.Geometric.PointPicardClassInjectivity.parameterPicardClass_complex_injective M.abelianScheme Q eA
    (p.pointBundleClass_injective U V hdeg jU jV heU heV hcube Q recover)
  have hdual := p.parameterPicardClass_dual_injective U V hdeg jU jV heU heV hcube Q recover eA eD
  have hinj (T : Over Foundations.Scheme.ProjectiveSpace.complexBase) :
      Function.Injective (fun t : T ⟶ D.abelianScheme.scheme => RepresentationTheory.Theta.Geometric.ParameterizedPicardClass.parameterPicardClass Q t) :=
    RepresentationTheory.Theta.Geometric.ArbitraryTestPicardInjectivity.parameterPicardClass_arbitraryTest_injective M.abelianScheme Q eA hdual hcomplex T
      (p.parameterPicardHom (RepresentationTheory.Theta.Geometric.AlgebraicQuotient.algebraicThetaQuotient jU.left jV.left) hcube Q recover T) (fun _ => rfl)
  refine ⟨RepresentationTheory.Theta.Geometric.AlgebraicQuotient.algebraicThetaQuotient jU.left jV.left, Q, hhom, hamp,
    M.nativeThetaChernForm_trace U V jU jV heU heV hdeg,
    IsogenyKernel.ReferenceLatticeIsogeny.homogeneousParameterMap_mono Q hhom hinj, ?_,
    RepresentationTheory.Theta.Geometric.ParameterizedHomogeneousPicard.parameterHomogeneousPicardClass_one M.abelianScheme Q hhom eD, ⟨recover⟩, ⟨eD⟩, ⟨eA⟩⟩
  exact p.nativeHomogeneousPointPicardClass_bijective U V hdeg jU jV heU heV Q recover hhom

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference
