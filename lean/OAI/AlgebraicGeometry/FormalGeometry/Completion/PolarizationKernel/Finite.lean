import OAI.AlgebraicGeometry.FormalGeometry.Completion.PolarizationKernel.Proper
import OAI.AlgebraicGeometry.FormalGeometry.Completion.PolarizationKernel.SymmetricRestriction
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.AmpleLineBundles
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.AffinePullback
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.Ample

/-! # Finite -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.PolarizationKernel.Finite

noncomputable section

/-! The actual fppf polarization kernel of an ample line bundle is
finite, including its nonreduced scheme structure. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory
open scoped _root_.CategoryTheory.MonObj

namespace Construction

universe u
variable {K : Type u} [Field K] [IsAlgClosed K]
  (A : Over (Spec (CommRingCat.of K))) [GrpObj A] [IsCommMonObj A]
  [IsProper A.hom] [Smooth A.hom] [GeometricallyIntegral A.hom]
  (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.left)

theorem polarizationKernelInclusion_relative_zero :
    Polarization.PicardMap.Construction.polarizationRelativeSection A L (OverRepresentation.Construction.polarizationKernelInclusion A L) =
      AbelianModuli.HilbertConstruction.Picard.PicardSheaf.trivialPicardClass A (OverRepresentation.Construction.polarizationKernelOver A L) := by
  apply (Has.Construction.polarizationKernel_hasLift_iff A L (OverRepresentation.Construction.polarizationKernelInclusion A L)).mp
  exact ⟨𝟙 (Has.Construction.polarizationKernel A L)⟩

theorem polarizationKernel_finite (hL : L.IsAmple) : IsFinite (OverRepresentation.Construction.polarizationKernelOver A L).hom := by
  let T := OverRepresentation.Construction.polarizationKernelOver A L
  let i := OverRepresentation.Construction.polarizationKernelInclusion A L
  have : IsLocallyNoetherian T.left := LocallyOfFiniteType.isLocallyNoetherian T.hom
  have : T.left.IsSeparated := Quotients.FiniteDescent.CartesianFamily.Construction.CartesianFamilyProjective.separated T.hom
  have : IsClosedImmersion i.left := inferInstanceAs (IsClosedImmersion (Has.Construction.polarizationKernel A L).hom)
  have : IsAffineHom (i⁻¹).left :=
    inferInstanceAs (IsAffineHom (i.left ≫ (GrpObj.inv (X := A)).left))
  obtain ⟨e⟩ := SymmetricRestriction.Construction.polarizationKernel_symmetricRestriction_trivial A L i
    (polarizationKernelInclusion_relative_zero A L)
  exact Quotients.FiniteDescent.Ample.Construction.AmpleFinite.of_trivial T ((L.pullback i.left).tensor (L.pullback (i⁻¹).left))
    ((hL.pullback_of_isAffineHom i.left).tensor_of_separated (hL.pullback_of_isAffineHom (i⁻¹).left)) e

end Construction

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.PolarizationKernel.Finite
