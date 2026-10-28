import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.DualPicardInjectivity
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ReferenceIntrinsic.ChernPairing
import OAI.RepresentationTheory.Theta.Geometric.ArbitraryTestPicardInjectivity
import OAI.RepresentationTheory.Theta.Geometric.ParameterizedHomogeneousPicard

/-! # Picard Monomorphism -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference

noncomputable section

section

/-! The original ample reference line bundle and its normalized
homogeneous difference family have the prescribed native Chern pairing
and separate arbitrary test schemes in the actual Picard sheaf. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E]
    [NumberField.IsCMField E] {s : ℕ} {P : Datum.RankThreePELDatum E s}
    {z : P.domain} {F : Fiber.ReferenceAnalyticFiber P z} {hP : P.IsAdmissible}
    {M : AlgebraicModel.ReferenceAlgebraicModel F hP} {D : DualModel.ReferenceDualModel F hP}
    (p : IsogenyKernel.ReferenceLatticeIsogeny M D)

local instance IsogenyKernel.ReferenceLatticeIsogeny.universalPicardSeparation_proper : IsProper D.abelianScheme.scheme.hom :=
  D.abelian.variety.presentation.projective.isProper
local instance IsogenyKernel.ReferenceLatticeIsogeny.universalPicardSeparation_finiteType : LocallyOfFiniteType D.abelianScheme.scheme.hom := by
  let : Smooth D.abelianScheme.scheme.hom := D.abelian.variety.presentation.smooth
  infer_instance

theorem IsogenyKernel.ReferenceLatticeIsogeny.parameterHomogeneousPicardClass_injective
    (Q : HilbertConstruction.Line.Bundles.LineBundle (D.abelianScheme.scheme ⊗ M.abelianScheme.scheme).left)
    (hQ : M.abelianScheme.IsHomogeneousPicardClass D.abelianScheme.scheme (HilbertConstruction.Line.Bundles.LineBundle.classOf Q))
    (hinj : ∀ T : Over Foundations.Scheme.ProjectiveSpace.complexBase,
      Function.Injective (fun t : T ⟶ D.abelianScheme.scheme => RepresentationTheory.Theta.Geometric.ParameterizedPicardClass.parameterPicardClass Q t))
    (T : Over Foundations.Scheme.ProjectiveSpace.complexBase) :
    Function.Injective (fun t : T ⟶ D.abelianScheme.scheme =>
      RepresentationTheory.Theta.Geometric.ParameterizedHomogeneousPicard.parameterHomogeneousPicardClass M.abelianScheme Q hQ t) := by
  intro a b h
  apply hinj T
  exact (RepresentationTheory.Theta.Geometric.ParameterizedHomogeneousPicard.parameterHomogeneousPicardClass_forget M.abelianScheme Q hQ a).symm.trans
    ((congrArg (M.abelianScheme.homogeneousPicardSheafInclusion.hom.app (.op T)) h).trans
      (RepresentationTheory.Theta.Geometric.ParameterizedHomogeneousPicard.parameterHomogeneousPicardClass_forget M.abelianScheme Q hQ b))

include p in
theorem IsogenyKernel.ReferenceLatticeIsogeny.exists_ample_marked_universally_separating_family :
    ∃ (L : HilbertConstruction.Line.Bundles.LineBundle M.abelianScheme.scheme.left)
      (Q : HilbertConstruction.Line.Bundles.LineBundle (D.abelianScheme.scheme ⊗ M.abelianScheme.scheme).left),
      L.IsAmple ∧
      (∀ u v : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E, Intrinsic.ChernPairing.nativeChernForm M.abelian L
        (M.nativeReferenceMarking u) (M.nativeReferenceMarking v) = P.traceForm u v) ∧
      M.abelianScheme.IsHomogeneousPicardClass D.abelianScheme.scheme (HilbertConstruction.Line.Bundles.LineBundle.classOf Q) ∧
      (∀ T : Over Foundations.Scheme.ProjectiveSpace.complexBase, RepresentationTheory.Theta.Geometric.ParameterizedPicardClass.parameterPicardClass Q (1 : T ⟶ D.abelianScheme.scheme) =
        HilbertConstruction.Picard.PicardSheaf.trivialPicardClass M.abelianScheme.scheme T) ∧
      (∀ (T : Over Foundations.Scheme.ProjectiveSpace.complexBase) (a b : T ⟶ D.abelianScheme.scheme),
        RepresentationTheory.Theta.Geometric.ParameterizedPicardClass.parameterPicardClass Q (a * b) = RepresentationTheory.Theta.Geometric.ParameterizedPicardClass.parameterPicardClass Q a * RepresentationTheory.Theta.Geometric.ParameterizedPicardClass.parameterPicardClass Q b) ∧
      (∀ T : Over Foundations.Scheme.ProjectiveSpace.complexBase,
        Function.Injective (fun t : T ⟶ D.abelianScheme.scheme => RepresentationTheory.Theta.Geometric.ParameterizedPicardClass.parameterPicardClass Q t)) ∧
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
  refine ⟨RepresentationTheory.Theta.Geometric.AlgebraicQuotient.algebraicThetaQuotient jU.left jV.left, Q, hamp,
    M.nativeThetaChernForm_trace U V jU jV heU heV hdeg, hhom,
    RepresentationTheory.Theta.Geometric.ParameterizedPicardClass.parameterPicardClass_one Q eD, ?_, ?_, ⟨recover⟩, ⟨eD⟩, ⟨eA⟩⟩
  · intro T a b
    exact (p.parameterPicardHom (RepresentationTheory.Theta.Geometric.AlgebraicQuotient.algebraicThetaQuotient jU.left jV.left) hcube Q recover T).map_mul a b
  · intro T
    exact RepresentationTheory.Theta.Geometric.ArbitraryTestPicardInjectivity.parameterPicardClass_arbitraryTest_injective M.abelianScheme Q eA hdual hcomplex T
      (p.parameterPicardHom (RepresentationTheory.Theta.Geometric.AlgebraicQuotient.algebraicThetaQuotient jU.left jV.left) hcube Q recover T) (fun _ => rfl)

end

/-! The constructed normalized reference Poincare family embeds the
actual represented parameter functor into the homogeneous Picard sheaf.
Surjectivity, and hence full representability, remains to be constructed. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E]
    [NumberField.IsCMField E] {s : ℕ} {P : Datum.RankThreePELDatum E s}
    {z : P.domain} {F : Fiber.ReferenceAnalyticFiber P z} {hP : P.IsAdmissible}
    {M : AlgebraicModel.ReferenceAlgebraicModel F hP} {D : DualModel.ReferenceDualModel F hP}
    (p : IsogenyKernel.ReferenceLatticeIsogeny M D)

theorem IsogenyKernel.ReferenceLatticeIsogeny.homogeneousParameterMap_mono
    (Q : HilbertConstruction.Line.Bundles.LineBundle (D.abelianScheme.scheme ⊗ M.abelianScheme.scheme).left)
    (hQ : M.abelianScheme.IsHomogeneousPicardClass D.abelianScheme.scheme (HilbertConstruction.Line.Bundles.LineBundle.classOf Q))
    (hinj : ∀ T : Over Foundations.Scheme.ProjectiveSpace.complexBase,
      Function.Injective (fun t : T ⟶ D.abelianScheme.scheme => RepresentationTheory.Theta.Geometric.ParameterizedPicardClass.parameterPicardClass Q t)) :
    Mono (RepresentationTheory.Theta.Geometric.ParameterizedHomogeneousPicard.homogeneousParameterMap M.abelianScheme Q hQ) := by
  have hcomponent (T : (Over Foundations.Scheme.ProjectiveSpace.complexBase)ᵒᵖ) : Mono ((RepresentationTheory.Theta.Geometric.ParameterizedHomogeneousPicard.homogeneousParameterMap M.abelianScheme Q hQ).app T) := by
    apply ConcreteCategory.mono_of_injective
    intro a b h
    apply ULift.ext
    exact IsogenyKernel.ReferenceLatticeIsogeny.parameterHomogeneousPicardClass_injective Q hQ hinj T.unop h
  exact NatTrans.mono_of_mono_app (RepresentationTheory.Theta.Geometric.ParameterizedHomogeneousPicard.homogeneousParameterMap M.abelianScheme Q hQ)

include p in
theorem IsogenyKernel.ReferenceLatticeIsogeny.exists_normalized_picard_monomorphism :
    ∃ (L : HilbertConstruction.Line.Bundles.LineBundle M.abelianScheme.scheme.left)
      (Q : HilbertConstruction.Line.Bundles.LineBundle (D.abelianScheme.scheme ⊗ M.abelianScheme.scheme).left)
      (hQ : M.abelianScheme.IsHomogeneousPicardClass D.abelianScheme.scheme (HilbertConstruction.Line.Bundles.LineBundle.classOf Q)),
      L.IsAmple ∧
      (∀ u v : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E, Intrinsic.ChernPairing.nativeChernForm M.abelian L
        (M.nativeReferenceMarking u) (M.nativeReferenceMarking v) = P.traceForm u v) ∧
      Mono (RepresentationTheory.Theta.Geometric.ParameterizedHomogeneousPicard.homogeneousParameterMap M.abelianScheme Q hQ) ∧
      (∀ T : Over Foundations.Scheme.ProjectiveSpace.complexBase, RepresentationTheory.Theta.Geometric.ParameterizedHomogeneousPicard.parameterHomogeneousPicardClass M.abelianScheme Q hQ
        (1 : T ⟶ D.abelianScheme.scheme) = M.abelianScheme.trivialHomogeneousPicardClass T) ∧
      Nonempty ((Q.pullback (p.isogeny.hom ⊗ₘ 𝟙 M.abelianScheme.scheme).left).sheaf ≅
        (RepresentationTheory.Theta.Geometric.AbelianDifferenceBundle.abelianDifferenceBundle M.abelianScheme L).sheaf) ∧
      Nonempty ((Q.pullback (lift (1 : M.abelianScheme.scheme ⟶ D.abelianScheme.scheme)
        (𝟙 M.abelianScheme.scheme)).left).sheaf ≅ HilbertConstruction.Line.Bundles.structureModule M.abelianScheme.scheme.left) ∧
      Nonempty ((Q.pullback (lift (𝟙 D.abelianScheme.scheme)
        (1 : D.abelianScheme.scheme ⟶ M.abelianScheme.scheme)).left).sheaf ≅
          HilbertConstruction.Line.Bundles.structureModule D.abelianScheme.scheme.left) := by
  obtain ⟨L, Q, hL, hchern, hQ, _, _, hinj, hr, ⟨eD⟩, heA⟩ :=
    p.exists_ample_marked_universally_separating_family
  exact ⟨L, Q, hQ, hL, hchern, IsogenyKernel.ReferenceLatticeIsogeny.homogeneousParameterMap_mono Q hQ hinj,
    RepresentationTheory.Theta.Geometric.ParameterizedHomogeneousPicard.parameterHomogeneousPicardClass_one M.abelianScheme Q hQ eD, hr, ⟨eD⟩, heA⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference
