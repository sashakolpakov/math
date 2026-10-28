import OAI.AlgebraicGeometry.Picard.ThetaConstruction.SameChernTranslationStabilizer
import OAI.AlgebraicGeometry.Picard.ThetaConstruction.ComplexPicardConstruction
import OAI.RepresentationTheory.Theta.Geometric.DifferencePicardClasses
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Picard.BaseBundleTriviality
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Isogeny.KernelScheme

/-! # Intrinsic Translation Kernel -/

namespace OAI.AlgebraicGeometry.Picard.ThetaConstruction.IntrinsicTranslationKernel.Geometric

noncomputable section

/-! The all-test translation stabilizer of any line with the original
primitive Chern pairing is exactly the kernel of the constructed
integral-dual isogeny. Both the isogeny and the comparison are built
from the actual theta family. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Picard.BaseBundleTriviality OAI.RepresentationTheory.Theta.Geometric.DifferencePicardClasses

private theorem mapped_difference_of_trivial_middle
    {M N : Type*} [CommGroup M] [CommGroup N] (f : M →* N) (a b c : M) (hb : f b = 1) :
    f (a * b⁻¹ * c⁻¹) = f a * (f c)⁻¹ := by
  simp only [map_mul, map_inv, hb, inv_one, mul_one]

theorem nativeDifference_picard_zero_iff_translation {g : ℕ}
    (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g Foundations.Scheme.ProjectiveSpace.complexBase) (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.scheme.left)
    {U : Over Foundations.Scheme.ProjectiveSpace.complexBase} (a : U ⟶ A.scheme) :
    RepresentationTheory.Theta.Geometric.ParameterizedPicardClass.parameterPicardClass (RepresentationTheory.Theta.Geometric.AbelianDifferenceBundle.abelianDifferenceBundle A L) a = AbelianModuli.HilbertConstruction.Picard.PicardSheaf.trivialPicardClass A.scheme U ↔
      A.TranslationInvariant a (AbelianModuli.ReferenceFamily.HomogeneousLinePowers.constantLineFamily A U (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L)) := by
  let picardQuotient := Homomorphisms.RelativeGroup.Construction.toRelativePicardHom A.scheme U
  let q := AbelianModuli.ReferenceFamily.HomogeneousLinePowers.constantLineFamily A U (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L)
  have hb : picardQuotient (RepresentationTheory.Theta.Geometric.Picard.PicardPullback.picardPullback (fst U A.scheme).left (RepresentationTheory.Theta.Geometric.Picard.PicardPullback.picardPullback a.left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L))) = 1 :=
    (AbelianModuli.HilbertConstruction.Picard.BaseBundleTriviality.baseBundle_relativePicardClass_trivial A.scheme U (L.pullback a.left)).trans
      (Homomorphisms.RelativeGroup.Construction.trivialPicardClass_eq_one A.scheme U)
  have hv : RepresentationTheory.Theta.Geometric.ParameterizedPicardClass.parameterPicardClass (RepresentationTheory.Theta.Geometric.AbelianDifferenceBundle.abelianDifferenceBundle A L) a =
      picardQuotient (RepresentationTheory.Theta.Geometric.Picard.PicardPullback.picardPullback (A.translation a).left q) * (picardQuotient q)⁻¹ := by
    change picardQuotient (RepresentationTheory.Theta.Geometric.ParameterizedPicardClass.parameterLineClass (RepresentationTheory.Theta.Geometric.AbelianDifferenceBundle.abelianDifferenceBundle A L) a) = _
    exact (congrArg picardQuotient (RepresentationTheory.Theta.Geometric.DifferencePicardClasses.parameterDifference_class A L a)).trans
      (@mapped_difference_of_trivial_middle (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass (U ⊗ A.scheme).left)
        (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.PicardSections A.scheme U) (Homomorphisms.SchemeGroup.Construction.lineBundleClassCommGroup _) inferInstance
        picardQuotient _ _ _ hb)
  rw [hv, Homomorphisms.RelativeGroup.Construction.trivialPicardClass_eq_one, mul_inv_eq_one]
  rfl

theorem descendedDifference_translation_iff_kernel {g h : ℕ}
    (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g Foundations.Scheme.ProjectiveSpace.complexBase) (B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme h Foundations.Scheme.ProjectiveSpace.complexBase)
    (p : A.scheme ⟶ B.scheme) (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.scheme.left)
    (Q : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (B.scheme ⊗ A.scheme).left)
    (recover : (Q.pullback (p ⊗ₘ 𝟙 A.scheme).left).sheaf ≅ (RepresentationTheory.Theta.Geometric.AbelianDifferenceBundle.abelianDifferenceBundle A L).sheaf)
    (zero : (Q.pullback (lift (1 : A.scheme ⟶ B.scheme) (𝟙 A.scheme)).left).sheaf ≅
      AbelianModuli.HilbertConstruction.Line.Bundles.structureModule A.scheme.left)
    (hinj : ∀ U : Over Foundations.Scheme.ProjectiveSpace.complexBase, Function.Injective (fun t : U ⟶ B.scheme => RepresentationTheory.Theta.Geometric.ParameterizedPicardClass.parameterPicardClass Q t))
    (U : Over Foundations.Scheme.ProjectiveSpace.complexBase) (a : U ⟶ A.scheme) :
    A.TranslationInvariant a (AbelianModuli.ReferenceFamily.HomogeneousLinePowers.constantLineFamily A U (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L)) ↔ a ≫ p = 1 := by
  have hp : RepresentationTheory.Theta.Geometric.ParameterizedPicardClass.parameterPicardClass Q (a ≫ p) = RepresentationTheory.Theta.Geometric.ParameterizedPicardClass.parameterPicardClass (RepresentationTheory.Theta.Geometric.AbelianDifferenceBundle.abelianDifferenceBundle A L) a :=
    congrArg ((AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A.scheme).app (.op U))
      ((RepresentationTheory.Theta.Geometric.ParameterizedPicardClass.parameterLineClass_baseChange Q p a).trans (RepresentationTheory.Theta.Geometric.DifferencePicardClasses.parameterLineClass_congr _ _ recover a))
  have hz := RepresentationTheory.Theta.Geometric.ParameterizedPicardClass.parameterPicardClass_one Q zero U
  rw [← nativeDifference_picard_zero_iff_translation, ← hp, ← hz]
  exact ⟨fun h => hinj U h, congrArg (RepresentationTheory.Theta.Geometric.ParameterizedPicardClass.parameterPicardClass Q)⟩

namespace AlgebraicPeriodModel
variable {g : ℕ} {E : DefinitionsIntegral.IntegralMatrix g} {T : DefinitionsIntegral.MarkedPolarizedTorus g E}
    (M : PeriodModel.Geometric.AlgebraicPeriodModel T)

theorem _root_.OAI.AlgebraicGeometry.Picard.ThetaConstruction.PeriodModel.Geometric.AlgebraicPeriodModel.exists_primitive_translation_kernel (hE : E.transpose = -E)
    (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle M.abelian.toOver.left)
    (hL : ∀ l m : T.lattice,
      AbelianModuli.ReferenceFamily.Intrinsic.ChernPairing.nativeChernForm M.abelian L (M.nativeIntegralPeriod l) (M.nativeIntegralPeriod m) =
        (DefinitionsIntegral.Geometric.integralLatticeForm T l m : ℚ)) :
    ∃ (N : IntegralDualModel.Geometric.IntegralDualAlgebraicModel T) (p : IntegralDualIsogenyKernel.Geometric.IntegralDualLatticeIsogeny M N),
      ∀ (U : Over Foundations.Scheme.ProjectiveSpace.complexBase) (a : U ⟶ M.abelianScheme.scheme),
        M.abelianScheme.TranslationInvariant a
          (AbelianModuli.ReferenceFamily.HomogeneousLinePowers.constantLineFamily M.abelianScheme U (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L)) ↔ a ≫ p.isogeny.hom = 1 := by
  obtain ⟨N, ⟨p⟩⟩ := IntegralDualIsogenyKernel.Geometric.exists_integralDualLatticeIsogeny M
  obtain ⟨K, Q, _hQ, _hamp, hpair, _hmono, hinj, _hcomplex, ⟨recover⟩, ⟨eN⟩, _eM⟩ :=
    p.exists_normalized_complex_picard_classification hE
  refine ⟨N, p, ?_⟩
  intro U a
  exact (M.sameIntegralPairing_translationInvariant_iff hE L K
    (fun l m => (hL l m).trans (hpair l m).symm) U a).trans
      (descendedDifference_translation_iff_kernel M.abelianScheme N.abelianScheme p.isogeny.hom
        K Q recover eN hinj U a)

end AlgebraicPeriodModel

end

end OAI.AlgebraicGeometry.Picard.ThetaConstruction.IntrinsicTranslationKernel.Geometric
