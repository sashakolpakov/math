import OAI.AlgebraicGeometry.SheafCohomology.Projective.BaseCechAllDegrees

/-! # Base Cech Vanishing Transfer -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.BaseCechVanishingTransfer

noncomputable section

/-! Transfer of ordered affine-cover exactness to actual sheaf cohomology. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
universe u

theorem orderedBaseCech_exactAt_subsingleton_H
    {X S : Scheme.{u}} [X.IsSeparated] (π : X ⟶ S)
    (M : X.Modules) [M.IsQuasicoherent]
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) (hU : IsOpenCover U)
    (hUaff : ∀ i, IsAffineOpen (U i)) (n : ℕ)
    (h : (OrderedBaseCech.Scheme.Modules.orderedBaseCechComplex π M U).ExactAt n) :
    Subsingleton (AffineH.Projective.H M n) := by
  let := BaseCechBridge.baseCohomologyModule π M n
  have : Subsingleton ((OrderedBaseCech.Scheme.Modules.orderedBaseCechComplex π M U).homology n) :=
    ModuleCat.subsingleton_of_isZero h.isZero_homology
  exact (BaseCechAllDegrees.orderedBaseCechHomologyAffineHLinearEquiv π M U hU hUaff n).symm.injective.subsingleton

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.BaseCechVanishingTransfer
