import OAI.AlgebraicGeometry.Picard.ThetaConstruction.ComplexPicardConstruction
import OAI.AlgebraicGeometry.Picard.ThetaConstruction.StructureBound
import OAI.RepresentationTheory.Theta.Geometric.Dual.PicardData
import OAI.RepresentationTheory.Theta.Geometric.Relative.ParameterSeparation
import OAI.RepresentationTheory.Theta.Geometric.AbelianIntegrality

/-! # Relative -/

namespace OAI.AlgebraicGeometry.Picard.ThetaConstruction

noncomputable section

/-! The actual primitive ThetaConstruction theta family represents the homogeneous
Picard sheaf on arbitrary complex test schemes. Its relative universality
follows from the constructed separation, complex classification and
the actual algebraic structure-sheaf H1 bound. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

variable {dim : ℕ} {E : DefinitionsIntegral.IntegralMatrix dim} {T : DefinitionsIntegral.MarkedPolarizedTorus dim E}
    {M : PeriodModel.Geometric.AlgebraicPeriodModel T} {N : IntegralDualModel.Geometric.IntegralDualAlgebraicModel T}

theorem IntegralDualIsogenyKernel.Geometric.IntegralDualLatticeIsogeny.exists_primitive_relative_picard_classification
    (p : IntegralDualIsogenyKernel.Geometric.IntegralDualLatticeIsogeny M N) (hE : E.transpose = -E) :
    ∃ (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle M.abelianScheme.scheme.left)
      (Q : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (N.abelianScheme.scheme ⊗ M.abelianScheme.scheme).left)
      (hQ : M.abelianScheme.IsHomogeneousPicardClass N.abelianScheme.scheme (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf Q)),
      L.IsAmple ∧
      (∀ l m : T.lattice, AbelianModuli.ReferenceFamily.Intrinsic.ChernPairing.nativeChernForm M.abelian L
        (M.nativeIntegralPeriod l) (M.nativeIntegralPeriod m) = (DefinitionsIntegral.Geometric.integralLatticeForm T l m : ℚ)) ∧
      IsIso (RepresentationTheory.Theta.Geometric.ParameterizedHomogeneousPicard.homogeneousParameterMap M.abelianScheme Q hQ) ∧
      Nonempty ((Q.pullback (p.isogeny.hom ⊗ₘ 𝟙 M.abelianScheme.scheme).left).sheaf ≅
        (RepresentationTheory.Theta.Geometric.AbelianDifferenceBundle.abelianDifferenceBundle M.abelianScheme L).sheaf) ∧
      Nonempty ((Q.pullback (lift (1 : M.abelianScheme.scheme ⟶ N.abelianScheme.scheme)
        (𝟙 M.abelianScheme.scheme)).left).sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule M.abelianScheme.scheme.left) ∧
      Nonempty ((Q.pullback (lift (𝟙 N.abelianScheme.scheme)
        (1 : N.abelianScheme.scheme ⟶ M.abelianScheme.scheme)).left).sheaf ≅
          AbelianModuli.HilbertConstruction.Line.Bundles.structureModule N.abelianScheme.scheme.left) := by
  obtain ⟨L, Q, hQ, hL, hchern, hmono, _hinj, hpoints, hrecovery, ⟨eN⟩, ⟨eM⟩⟩ :=
    p.exists_normalized_complex_picard_classification hE
  let : IsProper M.abelian.toOver.hom := M.abelian.variety.presentation.projective.isProper
  let : Smooth M.abelian.toOver.hom := M.abelian.variety.presentation.smooth
  let : GeometricallyIntegral M.abelian.toOver.hom := RepresentationTheory.Theta.Geometric.AbelianIntegrality.abelian_geometricallyIntegral M.abelian
  let RQ : FormalGeometry.Completion.Rigidified.ProductLine.Construction.RigidifiedProductLine M.abelianScheme.scheme N.abelianScheme.scheme := ⟨Q, eM⟩
  let := hmono
  have hinj : ∀ U : Over Foundations.Scheme.ProjectiveSpace.complexBase, Function.Injective (RQ.relativeValue (T := U)) :=
    RepresentationTheory.Theta.Geometric.Relative.ParameterSeparation.relativeValue_injective_of_homogeneous_mono M.abelianScheme RQ hQ
  have hIso : IsIso (RepresentationTheory.Theta.Geometric.ParameterizedHomogeneousPicard.homogeneousParameterMap M.abelianScheme Q hQ) :=
    RepresentationTheory.Theta.Geometric.HomogeneousPicardUniversality.homogeneousParameterMap_isIso M.abelian N.abelianScheme RQ hinj hQ hpoints.surjective
      M.periodStructureH1_finrank_le_dimension
  exact ⟨L, Q, hQ, hL, hchern, hIso, hrecovery, ⟨eN⟩, ⟨eM⟩⟩

end

end OAI.AlgebraicGeometry.Picard.ThetaConstruction
