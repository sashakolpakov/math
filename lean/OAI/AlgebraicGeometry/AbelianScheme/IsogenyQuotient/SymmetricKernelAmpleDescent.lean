import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.GroupHomAmpleness
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.TranslationSymmetricDescent
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Comparison
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.Powers
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PointLineBundleTriviality

/-! # Symmetric Kernel Ample Descent -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.SymmetricKernelAmpleDescent.Construction

noncomputable section

/-! Effective descent of an inducing line with symmetric kernel
translation defect produces an ample quotient line, with an actual
pullback isomorphism and a frame at the quotient identity. The defect
symmetry remains the explicit geometric lemma to be proved from isotropy. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.Powers OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Comparison.Bundle OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme
open OAI.AlgebraicGeometry.Picard.PoincareBundle.NormalizedKernelTranslation OAI.AlgebraicGeometry.Picard.PoincareBundle.Subgroup.DefectParameters

universe u

attribute [local instance] Picard.PoincareBundle.Kernel.Scheme.kernelGroup Picard.PoincareBundle.Kernel.Scheme.kernelGroup_commutative

theorem exists_ample_line_of_symmetric_kernel_transport
    {k : Type u} [Field k] [IsAlgClosed k]
    {A B : Over (Spec (.of k))} [GrpObj A] [IsCommMonObj A] [GrpObj B]
    [IsProper A.hom] [IsIntegral A.left] [IsLocallyNoetherian B.left]
    (f : A ⟶ B) [IsMonHom f] [IsFinite f.left] [Flat f.left] [Surjective f.left]
    (L : Picard.PoincareBundle.Line.Bundles.LineBundle A.left) (hL : (Picard.PoincareBundle.Line.Comparison.Bundle.toShared L).IsAmple)
    (t : Picard.PoincareBundle.Line.Fibers.fiber L (snd (Picard.PoincareBundle.Kernel.Scheme.kernelObject f) A) ≅ Picard.PoincareBundle.Line.Fibers.fiber L (Picard.PoincareBundle.NormalizedKernelTranslation.action (Picard.PoincareBundle.Kernel.Scheme.kernelInclusion f)))
    (hs : ∀ (T : Over (Spec (.of k))) (a b : T ⟶ Picard.PoincareBundle.Kernel.Scheme.kernelObject f),
      Picard.PoincareBundle.Subgroup.DefectParameters.value (Picard.PoincareBundle.Kernel.Scheme.kernelInclusion f) L t a b = Picard.PoincareBundle.Subgroup.DefectParameters.value (Picard.PoincareBundle.Kernel.Scheme.kernelInclusion f) L t b a) :
    ∃ M : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle B.left,
      M.IsAmple ∧ Nonempty ((M.pullback f.left).sheaf ≅ L.sheaf) ∧
        Nonempty ((M.pullback η[B].left).sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule (Spec (.of k))) := by
  have : ConnectedSpace B.left := f.left.surjective.connectedSpace f.left.continuous
  obtain ⟨M, ⟨e⟩⟩ := Picard.PoincareBundle.Kernel.TranslationSymmetricDescent.exists_descended_line f L t hs
  refine ⟨Picard.PoincareBundle.Line.Comparison.Bundle.toShared M, GroupHomAmpleness.Construction.finiteFlat_groupHom_isAmple_of_pullback f (Picard.PoincareBundle.Line.Comparison.Bundle.toShared M)
    (hL.of_iso e.symm), ⟨e⟩, ?_⟩
  have : Subsingleton (𝟙_ (Over (Spec (.of k)))).left :=
    inferInstanceAs (Subsingleton (Spec (.of k)))
  have : Nonempty (𝟙_ (Over (Spec (.of k)))).left :=
    inferInstanceAs (Nonempty (Spec (.of k)))
  exact ((Picard.PoincareBundle.Line.Comparison.Bundle.toShared M).pullback η[B].left).exists_trivialization_of_subsingleton

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.SymmetricKernelAmpleDescent.Construction
