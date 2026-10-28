import OAI.AlgebraicGeometry.Picard.PoincareBundle.TranslationSymmetryIndependence
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Symmetric.KernelLineDescent

/-! # Translation Symmetric Descent -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.TranslationSymmetricDescent

noncomputable section

/-! Descent requires symmetry of the original translation defect; normalization adds no hypothesis. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers OAI.AlgebraicGeometry.Picard.PoincareBundle.NormalizedKernelTranslation OAI.AlgebraicGeometry.Picard.PoincareBundle.Subgroup.DefectParameters

attribute [local instance] Kernel.Scheme.kernelGroup Kernel.Scheme.kernelGroup_commutative

variable {k : Type u} [Field k] [IsAlgClosed k]
  {A B : Over (Spec (.of k))} [GrpObj A] [IsCommMonObj A] [GrpObj B]
  [IsProper A.hom] [IsIntegral A.left] [IsLocallyNoetherian B.left]
  (f : A ⟶ B) [IsMonHom f] [IsFinite f.left] [Flat f.left] [Surjective f.left]
  (L : Line.Bundles.LineBundle A.left)
  (t : Line.Fibers.fiber L (snd (Kernel.Scheme.kernelObject f) A) ≅ Line.Fibers.fiber L (NormalizedKernelTranslation.action (Kernel.Scheme.kernelInclusion f)))

/-- Symmetry of the original defect suffices for effective line descent, independently of normalization. -/
theorem exists_descended_line
    (hs : ∀ (T : Over (Spec (.of k))) (a b : T ⟶ Kernel.Scheme.kernelObject f),
      Subgroup.DefectParameters.value (Kernel.Scheme.kernelInclusion f) L t a b = Subgroup.DefectParameters.value (Kernel.Scheme.kernelInclusion f) L t b a) :
    ∃ M : Line.Bundles.LineBundle B.left, Nonempty ((Scheme.Modules.pullback f.left).obj M.sheaf ≅ L.sheaf) := by
  apply Symmetric.KernelLineDescent.exists_descended_line f L t
  intro T a b
  exact (TranslationSymmetryIndependence.normalized_symmetry_iff (Kernel.Scheme.kernelInclusion f) L t a b).mpr
    (hs T a b)

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.TranslationSymmetricDescent
