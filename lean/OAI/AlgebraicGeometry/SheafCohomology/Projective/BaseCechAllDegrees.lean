import OAI.AlgebraicGeometry.SheafCohomology.Projective.BaseFiniteness
import OAI.AlgebraicGeometry.SheafCohomology.Cech.ZeroSurjective

/-! # Base Cech All Degrees -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.BaseCechAllDegrees

noncomputable section

/-! The base-linear affine-cover Čech comparison in every degree, including zero. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
universe u

theorem baseHZeroCechLinear_surjective {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    {ι : Type u} (U : ι → X.Opens) (hU : IsOpenCover U) :
    Function.Surjective (BaseFiniteness.baseHZeroCechLinear π M U) :=
  (Cech.ZeroSurjective.TopCat.Sheaf.cechTopSectionsToHZero_surjective U
    ((SheafOfModules.toSheaf X.ringCatSheaf).obj M) hU.iSup_eq_top).comp
      (AffineH.Projective.hZeroCanonicalLinearEquivGlobalSections M).surjective

def baseCechHomologyAffineHLinearEquiv
    {X S : Scheme.{u}} [X.IsSeparated] (π : X ⟶ S)
    (M : X.Modules) [M.IsQuasicoherent]
    {ι : Type u} (U : ι → X.Opens) (hU : IsOpenCover U)
    (hUaff : ∀ i, IsAffineOpen (U i)) (n : ℕ) :
    letI := BaseCechBridge.baseCohomologyModule π M n
    (Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechComplex π M U).homology n ≃ₗ[Γ(S, ⊤)]
      AffineH.Projective.H M n := by
  cases n with
  | zero =>
      letI := BaseCechBridge.baseCohomologyModule π M 0
      letI := BaseCechLinearBridge.nativeCechBaseModule π M U 0
      exact (BaseCechLinearBridge.baseCechHomologyNativeLinearEquiv π M U 0).trans
        (LinearEquiv.ofBijective (BaseFiniteness.baseHZeroCechLinear π M U)
          ⟨BaseFiniteness.baseHZeroCechLinear_injective π M U hU,
            baseHZeroCechLinear_surjective π M U hU⟩).symm
  | succ n => exact BaseCechBridge.baseCechHomologyAffineHSuccLinearEquiv π M U hU hUaff n

def orderedBaseCechHomologyAffineHLinearEquiv
    {X S : Scheme.{u}} [X.IsSeparated] (π : X ⟶ S)
    (M : X.Modules) [M.IsQuasicoherent]
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) (hU : IsOpenCover U)
    (hUaff : ∀ i, IsAffineOpen (U i)) (n : ℕ) :
    letI := BaseCechBridge.baseCohomologyModule π M n
    (OrderedBaseCech.Scheme.Modules.orderedBaseCechComplex π M U).homology n ≃ₗ[Γ(S, ⊤)]
      AffineH.Projective.H M n := by
  letI := BaseCechBridge.baseCohomologyModule π M n
  exact (BaseCechHomotopyEquiv.Scheme.Modules.baseCechOrderedHomologyIso π M U n).symm.toLinearEquiv.trans
    (baseCechHomologyAffineHLinearEquiv π M U hU hUaff n)

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.BaseCechAllDegrees
