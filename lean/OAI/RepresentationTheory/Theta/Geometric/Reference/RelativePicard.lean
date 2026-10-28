import OAI.RepresentationTheory.Theta.Geometric.ReferenceComplexPicardConstruction
import OAI.RepresentationTheory.Theta.Geometric.FamilyReferenceStructureBound
import OAI.RepresentationTheory.Theta.Geometric.Dual.PicardData
import OAI.RepresentationTheory.Theta.Geometric.Relative.ParameterSeparation
import OAI.RepresentationTheory.Theta.Geometric.AbelianIntegrality

/-! # Relative Picard -/

namespace OAI.RepresentationTheory.Theta.Geometric.Reference.RelativePicard

noncomputable section

/-! The original reference theta construction represents the full
relative homogeneous Picard sheaf, on arbitrary tests. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    {s : ℕ} {P : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s} {z : P.domain}
    {F : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.Fiber.ReferenceAnalyticFiber P z} {hP : P.IsAdmissible}
    {M : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.AlgebraicModel.ReferenceAlgebraicModel F hP} {N : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.DualModel.ReferenceDualModel F hP}
    (p : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.IsogenyKernel.ReferenceLatticeIsogeny M N)

include p in
theorem exists_reference_relative_picard_classification :
    ∃ (L : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle M.abelianScheme.scheme.left)
      (Q : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (N.abelianScheme.scheme ⊗ M.abelianScheme.scheme).left)
      (hQ : M.abelianScheme.IsHomogeneousPicardClass N.abelianScheme.scheme (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf Q)),
      L.IsAmple ∧
      (∀ u v : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E, AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.ChernPairing.nativeChernForm M.abelian L
        (M.nativeReferenceMarking u) (M.nativeReferenceMarking v) = P.traceForm u v) ∧
      IsIso (ParameterizedHomogeneousPicard.homogeneousParameterMap M.abelianScheme Q hQ) ∧
      Nonempty ((Q.pullback (p.isogeny.hom ⊗ₘ 𝟙 M.abelianScheme.scheme).left).sheaf ≅
        (AbelianDifferenceBundle.abelianDifferenceBundle M.abelianScheme L).sheaf) ∧
      Nonempty ((Q.pullback (lift (1 : M.abelianScheme.scheme ⟶ N.abelianScheme.scheme)
        (𝟙 M.abelianScheme.scheme)).left).sheaf ≅ AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule M.abelianScheme.scheme.left) ∧
      Nonempty ((Q.pullback (lift (𝟙 N.abelianScheme.scheme)
        (1 : N.abelianScheme.scheme ⟶ M.abelianScheme.scheme)).left).sheaf ≅
          AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule N.abelianScheme.scheme.left) := by
  obtain ⟨L, Q, hQ, hL, hchern, hmono, hpoints, _, hrecovery, ⟨eN⟩, ⟨eM⟩⟩ :=
    p.exists_normalized_complex_picard_classification
  let : IsProper M.abelian.toOver.hom := M.abelian.variety.presentation.projective.isProper
  let : Smooth M.abelian.toOver.hom := M.abelian.variety.presentation.smooth
  let : GeometricallyIntegral M.abelian.toOver.hom := AbelianIntegrality.abelian_geometricallyIntegral M.abelian
  let RQ : AlgebraicGeometry.FormalGeometry.Completion.Rigidified.ProductLine.Construction.RigidifiedProductLine M.abelianScheme.scheme N.abelianScheme.scheme := ⟨Q, eM⟩
  let := hmono
  have hinj : ∀ T : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase, Function.Injective (RQ.relativeValue (T := T)) :=
    Relative.ParameterSeparation.relativeValue_injective_of_homogeneous_mono M.abelianScheme RQ hQ
  have hIso : IsIso (ParameterizedHomogeneousPicard.homogeneousParameterMap M.abelianScheme Q hQ) :=
    HomogeneousPicardUniversality.homogeneousParameterMap_isIso M.abelian N.abelianScheme RQ hinj hQ hpoints.surjective
      M.referenceStructureH1_finrank_le_dimension
  exact ⟨L, Q, hQ, hL, hchern, hIso, hrecovery, ⟨eN⟩, ⟨eM⟩⟩

end

end OAI.RepresentationTheory.Theta.Geometric.Reference.RelativePicard
