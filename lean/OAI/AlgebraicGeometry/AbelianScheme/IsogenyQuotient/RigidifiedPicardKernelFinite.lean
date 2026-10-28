import OAI.AlgebraicGeometry.FormalGeometry.Completion.Rigidified.PicardHomKernel
import OAI.AlgebraicGeometry.FormalGeometry.Completion.Rigidified.RelativeZeroTriviality
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.AffinePullback
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.Ample

/-! # Rigidified Picard Kernel Finite -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.RigidifiedPicardKernelFinite.Construction

noncomputable section

/-! A rigidified multiplicative Picard family with ample diagonal has
an actual finite scheme-theoretic kernel. No representing dual abelian
scheme is assumed: the zero scheme is constructed from normalized frames. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u
variable {k : Type u} [Field k] [IsAlgClosed k]
  {B : Over (Spec (.of k))} [GrpObj B] [IsCommMonObj B]
  [IsProper B.hom] [Smooth B.hom] [GeometricallyIntegral B.hom]
  [IsLocallyNoetherian B.left]
  (D : FormalGeometry.Completion.Rigidified.ProductLine.Construction.RigidifiedProductLine B B)

def rigidifiedDiagonalLine : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle B.left :=
  D.bundle.pullback (lift (𝟙 B) (𝟙 B)).left

theorem rigidifiedPicardKernel_diagonal_trivial :
    Nonempty (((rigidifiedDiagonalLine D).pullback D.zeroInclusion.left).sheaf ≅
      AbelianModuli.HilbertConstruction.Line.Bundles.structureModule D.zeroSchemeOver.left) := by
  let Z := D.zeroSchemeOver
  let i := D.zeroInclusion
  let j : Z ⟶ Z ⊗ B := lift (𝟙 Z) i
  have h : j ≫ (i ⊗ₘ 𝟙 B) = i ≫ lift (𝟙 B) (𝟙 B) := by
    apply CartesianMonoidalCategory.hom_ext
    · simp [j]
    · simp [j]
  obtain ⟨e⟩ := Quotient.exact
    (D.class_trivial_of_relative_zero i D.zeroInclusion_relative_zero)
  exact ⟨(Scheme.Modules.pullbackComp i.left (lift (𝟙 B) (𝟙 B)).left).app D.bundle.sheaf ≪≫
    (Scheme.Modules.pullbackCongr (congrArg Over.Hom.left h.symm)).app D.bundle.sheaf ≪≫
    (Scheme.Modules.pullbackComp j.left (i ⊗ₘ 𝟙 B).left).symm.app D.bundle.sheaf ≪≫
    (Scheme.Modules.pullback j.left).mapIso e ≪≫ AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso j.left⟩

theorem rigidifiedPicardKernel_isFinite (hgroup : D.ZeroIsSubgroup)
    (hample : (rigidifiedDiagonalLine D).IsAmple) : IsFinite D.zeroSchemeOver.hom := by
  let Z := D.zeroSchemeOver
  let i := D.zeroInclusion
  have : IsClosedImmersion i.left := D.zeroScheme_closed hgroup
  have : IsProper Z.hom := by
    rw [← i.w]
    infer_instance
  obtain ⟨e⟩ := rigidifiedPicardKernel_diagonal_trivial D
  exact Quotients.FiniteDescent.Ample.Construction.AmpleFinite.of_trivial Z ((rigidifiedDiagonalLine D).pullback i.left)
    (hample.pullback_of_isAffineHom i.left) e

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.RigidifiedPicardKernelFinite.Construction
