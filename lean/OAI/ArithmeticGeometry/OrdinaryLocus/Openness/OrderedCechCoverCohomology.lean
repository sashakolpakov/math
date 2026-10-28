import OAI.AlgebraicGeometry.Quotients.FiniteDescent.GlobalModel
import OAI.AlgebraicGeometry.SheafCohomology.Projective.BaseCechBridge
import OAI.AlgebraicGeometry.SheafCohomology.Projective.BaseCechHomotopyEquiv

/-! # Ordered Cech Cover Cohomology -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.OrderedCechCoverCohomology.Construction

noncomputable section

/-! Cohomology of ordered affine Cech covers, including the canonical degree-zero sections. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace Opposite
open _root_.AlgebraicGeometry.Scheme.Modules

universe u

variable {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
variable {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) (hU : iSup U = ⊤)

def orderedCechHZeroSectionsEquiv :
    (AlgebraicGeometry.SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.orderedBaseCechComplex π M U).homology 0 ≃ₗ[Γ(S, ⊤)]
      (AlgebraicGeometry.SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf π M).obj (op ⊤) := by
  let C : CochainComplex (ModuleCat.{u} Γ(S, ⊤)) ℕ := AlgebraicGeometry.SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.orderedBaseCechComplex π M U
  exact ((C.isoHomologyπ₀.symm ≪≫ AlgebraicGeometry.Quotients.FiniteDescent.CochainZero.Construction.CochainZeroCycles.cyclesIso C).toLinearEquiv).trans
    (AlgebraicGeometry.Quotients.FiniteDescent.OrderedCechZeroGluing.Construction.OrderedCechZeroCoordinates.sectionsEquiv π M U hU).symm

def orderedCechSheafHSuccLinearEquiv [X.IsSeparated] [M.IsQuasicoherent]
    (hUaff : ∀ i, IsAffineOpen (U i)) (n : ℕ) :
    letI := AlgebraicGeometry.SheafCohomology.Projective.BaseCechBridge.baseCohomologyModule π M (n + 1)
    (AlgebraicGeometry.SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.orderedBaseCechComplex π M U).homology (n + 1) ≃ₗ[Γ(S, ⊤)] AlgebraicGeometry.SheafCohomology.AffineH.Projective.H M (n + 1) := by
  letI := AlgebraicGeometry.SheafCohomology.Projective.BaseCechBridge.baseCohomologyModule π M (n + 1)
  exact (AlgebraicGeometry.SheafCohomology.Projective.BaseCechHomotopyEquiv.Scheme.Modules.baseCechOrderedHomologyIso π M U (n + 1)).symm.toLinearEquiv.trans
    (AlgebraicGeometry.SheafCohomology.Projective.BaseCechBridge.baseCechHomologyAffineHSuccLinearEquiv π M U (.mk hU) hUaff n)

def orderedCechCoverHomologyEquiv [X.IsSeparated] [M.IsQuasicoherent]
    (hUaff : ∀ i, IsAffineOpen (U i))
    {κ : Type u} [LinearOrder κ] (V : κ → X.Opens) (hV : iSup V = ⊤)
    (hVaff : ∀ i, IsAffineOpen (V i)) (n : ℕ) :
    (AlgebraicGeometry.SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.orderedBaseCechComplex π M U).homology n ≃ₗ[Γ(S, ⊤)]
      (AlgebraicGeometry.SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.orderedBaseCechComplex π M V).homology n := by
  cases n with
  | zero =>
      exact (orderedCechHZeroSectionsEquiv π M U hU).trans
        (orderedCechHZeroSectionsEquiv π M V hV).symm
  | succ n =>
      letI := AlgebraicGeometry.SheafCohomology.Projective.BaseCechBridge.baseCohomologyModule π M (n + 1)
      exact (orderedCechSheafHSuccLinearEquiv π M U hU hUaff n).trans
        (orderedCechSheafHSuccLinearEquiv π M V hV hVaff n).symm

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.OrderedCechCoverCohomology.Construction
