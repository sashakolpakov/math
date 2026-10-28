import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.ComplexPicardConstruction
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.DualLineUniversality

/-! # Infinitesimal Picard Construction -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference

noncomputable section

/-! The theta construction supplies the actual ample, marked family,
including complex-point classification and unique infinitesimal parameters.
Neither the family nor its separation and group laws are new inputs. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E]
    [NumberField.IsCMField E] {s : ℕ} {P : Datum.RankThreePELDatum E s}
    {z : P.domain} {F : Fiber.ReferenceAnalyticFiber P z} {hP : P.IsAdmissible}
    {M : AlgebraicModel.ReferenceAlgebraicModel F hP} {D : DualModel.ReferenceDualModel F hP}
    (p : IsogenyKernel.ReferenceLatticeIsogeny M D)

local instance IsogenyKernel.ReferenceLatticeIsogeny.infinitesimalPicard_proper : IsProper D.abelianScheme.scheme.hom :=
  D.abelian.variety.presentation.projective.isProper
local instance IsogenyKernel.ReferenceLatticeIsogeny.infinitesimalPicard_finiteType : LocallyOfFiniteType D.abelianScheme.scheme.hom := by
  let : Smooth D.abelianScheme.scheme.hom := D.abelian.variety.presentation.smooth
  infer_instance

include p in
theorem IsogenyKernel.ReferenceLatticeIsogeny.exists_normalized_infinitesimal_picard_classification :
    ∃ (L : HilbertConstruction.Line.Bundles.LineBundle M.abelianScheme.scheme.left)
      (Q : HilbertConstruction.Line.Bundles.LineBundle (D.abelianScheme.scheme ⊗ M.abelianScheme.scheme).left)
      (hQ : M.abelianScheme.IsHomogeneousPicardClass D.abelianScheme.scheme (HilbertConstruction.Line.Bundles.LineBundle.classOf Q)),
      L.IsAmple ∧
      (∀ u v : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E, Intrinsic.ChernPairing.nativeChernForm M.abelian L
        (M.nativeReferenceMarking u) (M.nativeReferenceMarking v) = P.traceForm u v) ∧
      (∀ T : Over Foundations.Scheme.ProjectiveSpace.complexBase,
        Function.Injective (fun t : T ⟶ D.abelianScheme.scheme => RepresentationTheory.Theta.Geometric.ParameterizedPicardClass.parameterPicardClass Q t)) ∧
      (∀ (T : Over Foundations.Scheme.ProjectiveSpace.complexBase) (a b : T ⟶ D.abelianScheme.scheme),
        RepresentationTheory.Theta.Geometric.ParameterizedPicardClass.parameterPicardClass Q (a * b) = RepresentationTheory.Theta.Geometric.ParameterizedPicardClass.parameterPicardClass Q a * RepresentationTheory.Theta.Geometric.ParameterizedPicardClass.parameterPicardClass Q b) ∧
      Function.Bijective (fun x : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints D.abelian.toOver =>
        RepresentationTheory.Theta.Geometric.ParameterizedHomogeneousPicard.parameterHomogeneousPicardClass M.abelianScheme Q hQ x) ∧
      Nonempty ((Q.pullback (p.isogeny.hom ⊗ₘ 𝟙 M.abelianScheme.scheme).left).sheaf ≅
        (RepresentationTheory.Theta.Geometric.AbelianDifferenceBundle.abelianDifferenceBundle M.abelianScheme L).sheaf) ∧
      Nonempty ((Q.pullback (lift (1 : M.abelianScheme.scheme ⟶ D.abelianScheme.scheme)
        (𝟙 M.abelianScheme.scheme)).left).sheaf ≅ HilbertConstruction.Line.Bundles.structureModule M.abelianScheme.scheme.left) ∧
      Nonempty ((Q.pullback (lift (𝟙 D.abelianScheme.scheme)
        (1 : D.abelianScheme.scheme ⟶ M.abelianScheme.scheme)).left).sheaf ≅
          HilbertConstruction.Line.Bundles.structureModule D.abelianScheme.scheme.left) ∧
      (∀ (K : HilbertConstruction.Line.Bundles.LineBundle (LieRanks.dualNumberTest ℂ ⊗ M.abelianScheme.scheme).left),
        Nonempty ((Scheme.Modules.pullback (RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction M.abelianScheme.scheme).left).obj K.sheaf ≅
          HilbertConstruction.Line.Bundles.structureModule M.abelianScheme.scheme.left) →
        ∃! t : DualOpen.Lifts.DualSchemePoints D.abelianScheme.scheme 1,
          Nonempty ((Q.pullback (t.val ⊗ₘ 𝟙 M.abelianScheme.scheme).left).sheaf ≅ K.sheaf)) := by
  obtain ⟨U, V, jU, jV, Q, _, hdeg, _, _, heU, heV, hamp, hcube, hhom, ⟨recover⟩, ⟨eD⟩, ⟨eA⟩⟩ :=
    p.exists_normalized_homogeneous_theta_difference
  have hcomplex := RepresentationTheory.Theta.Geometric.PointPicardClassInjectivity.parameterPicardClass_complex_injective M.abelianScheme Q eA
    (p.pointBundleClass_injective U V hdeg jU jV heU heV hcube Q recover)
  have hdual := p.parameterPicardClass_dual_injective U V hdeg jU jV heU heV hcube Q recover eA eD
  have hinj (T : Over Foundations.Scheme.ProjectiveSpace.complexBase) :
      Function.Injective (fun t : T ⟶ D.abelianScheme.scheme => RepresentationTheory.Theta.Geometric.ParameterizedPicardClass.parameterPicardClass Q t) :=
    RepresentationTheory.Theta.Geometric.ArbitraryTestPicardInjectivity.parameterPicardClass_arbitraryTest_injective M.abelianScheme Q eA hdual hcomplex T
      (p.parameterPicardHom (RepresentationTheory.Theta.Geometric.AlgebraicQuotient.algebraicThetaQuotient jU.left jV.left) hcube Q recover T) (fun _ => rfl)
  have hmul (T : Over Foundations.Scheme.ProjectiveSpace.complexBase) (a b : T ⟶ D.abelianScheme.scheme) :
      RepresentationTheory.Theta.Geometric.ParameterizedPicardClass.parameterPicardClass Q (a * b) = RepresentationTheory.Theta.Geometric.ParameterizedPicardClass.parameterPicardClass Q a * RepresentationTheory.Theta.Geometric.ParameterizedPicardClass.parameterPicardClass Q b :=
    (p.parameterPicardHom (RepresentationTheory.Theta.Geometric.AlgebraicQuotient.algebraicThetaQuotient jU.left jV.left) hcube Q recover T).map_mul a b
  refine ⟨RepresentationTheory.Theta.Geometric.AlgebraicQuotient.algebraicThetaQuotient jU.left jV.left, Q, hhom, hamp,
    M.nativeThetaChernForm_trace U V jU jV heU heV hdeg, hinj, hmul,
    p.nativeHomogeneousPointPicardClass_bijective U V hdeg jU jV heU heV Q recover hhom,
    ⟨recover⟩, ⟨eD⟩, ⟨eA⟩, ?_⟩
  intro K hK
  apply M.exists_unique_dualParameter_iso D Q eD eA ?_ (hinj _) K hK.some
  intro x y
  exact ((hmul _ x y).trans (Picard.Homomorphisms.RelativeGroup.Construction.toRelativePicard_mul M.abelianScheme.scheme _
    (RepresentationTheory.Theta.Geometric.ParameterizedPicardClass.parameterLineClass Q x) (RepresentationTheory.Theta.Geometric.ParameterizedPicardClass.parameterLineClass Q y)).symm).trans
      (HilbertConstruction.Picard.SheafMonoid.toRelativePicard_mul M.abelianScheme.scheme _ (RepresentationTheory.Theta.Geometric.ParameterizedPicardClass.parameterLineClass Q x) (RepresentationTheory.Theta.Geometric.ParameterizedPicardClass.parameterLineClass Q y))

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference
