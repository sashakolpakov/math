import OAI.AlgebraicGeometry.Picard.PoincareBundle.Symmetric.KernelLinearization
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.TransportLineDescent

/-! # Kernel Line Descent -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Symmetric.KernelLineDescent

noncomputable section

/-! Effective line descent from symmetry of the actual finite-kernel translation defect. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers OAI.AlgebraicGeometry.Picard.PoincareBundle.NormalizedKernelTranslation
open OAI.AlgebraicGeometry.Picard.PoincareBundle.NormalizedTranslationUnit OAI.AlgebraicGeometry.Picard.PoincareBundle.Subgroup.DefectParameters OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.KernelLinearization

attribute [local instance] Kernel.Scheme.kernelGroup Kernel.Scheme.kernelGroup_commutative

variable {k : Type u} [Field k] [IsAlgClosed k]
  {A B : Over (Spec (.of k))} [GrpObj A] [IsCommMonObj A] [GrpObj B]
  [IsProper A.hom] [IsIntegral A.left] [IsLocallyNoetherian B.left]
  (f : A ⟶ B) [IsMonHom f] [IsFinite f.left] [Flat f.left] [Surjective f.left]
  (L : Line.Bundles.LineBundle A.left)
  (t : Line.Fibers.fiber L (snd (Kernel.Scheme.kernelObject f) A) ≅ Line.Fibers.fiber L (NormalizedKernelTranslation.action (Kernel.Scheme.kernelInclusion f)))
  (hs : ∀ (T : Over (Spec (.of k))) (a b : T ⟶ Kernel.Scheme.kernelObject f),
    Subgroup.DefectParameters.value (Kernel.Scheme.kernelInclusion f) L (NormalizedTranslationUnit.translation (Kernel.Scheme.kernelInclusion f) L t) a b =
      Subgroup.DefectParameters.value (Kernel.Scheme.kernelInclusion f) L (NormalizedTranslationUnit.translation (Kernel.Scheme.kernelInclusion f) L t) b a)

include hs in
/-- The actual corrected transport descends the original line bundle to the quotient. -/
theorem exists_descended_line :
    ∃ M : Line.Bundles.LineBundle B.left, Nonempty ((Scheme.Modules.pullback f.left).obj M.sheaf ≅ L.sheaf) := by
  obtain ⟨D⟩ := KernelLinearization.exists_linearization f L t hs
  exact ⟨Kernel.TransportLineDescent.descendedLine f L D,
    ⟨Kernel.TransportLineDescent.pullbackIso f L D⟩⟩

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Symmetric.KernelLineDescent
