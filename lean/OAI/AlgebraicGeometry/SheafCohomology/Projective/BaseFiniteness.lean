import OAI.AlgebraicGeometry.SheafCohomology.Projective.BaseCechBridge
import OAI.AlgebraicGeometry.SheafCohomology.Projective.BaseCechHomotopyEquiv
import OAI.AlgebraicGeometry.SheafCohomology.CechZeroLinear

/-! # Base Finiteness -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.BaseFiniteness

noncomputable section

/-! Finiteness passes from native Čech homology to actual sheaf cohomology in all degrees. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
universe u

def baseHZeroCechLinear {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    {ι : Type u} (U : ι → X.Opens) :
    letI := BaseCechBridge.baseCohomologyModule π M 0
    letI := BaseCechLinearBridge.nativeCechBaseModule π M U 0
    AffineH.Projective.H M 0 →ₗ[Γ(S, ⊤)] (CechScalars.Projective.moduleCechCohomologyFunctor U 0).obj M := by
  letI := AffineH.Projective.globalSectionsCohomologyModule M 0
  letI := CechScalars.Projective.cechGlobalFunctionsModule M U 0
  let g := (CechZeroLinear.Projective.globalSectionsCechHZeroLinear M U).comp
    (AffineH.Projective.hZeroCanonicalLinearEquivGlobalSections M).toLinearMap
  letI := BaseCechBridge.baseCohomologyModule π M 0
  letI := BaseCechLinearBridge.nativeCechBaseModule π M U 0
  exact { g.toAddHom with map_smul' := fun r x => g.map_smul (π.appTop r) x }

theorem baseHZeroCechLinear_injective {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    {ι : Type u} (U : ι → X.Opens) (hU : IsOpenCover U) :
    Function.Injective (baseHZeroCechLinear π M U) :=
  (CechZeroLinear.Projective.globalSectionsCechHZeroLinear_injective M U hU).comp
    (AffineH.Projective.hZeroCanonicalLinearEquivGlobalSections M).injective

theorem baseCohomologyFinite_of_baseCech
    {X S : Scheme.{u}} [X.IsSeparated] (π : X ⟶ S)
    [IsNoetherianRing Γ(S, ⊤)] (M : X.Modules) [M.IsQuasicoherent]
    {ι : Type u} (U : ι → X.Opens) (hU : IsOpenCover U)
    (hUaff : ∀ i, IsAffineOpen (U i)) (n : ℕ)
    [Module.Finite Γ(S, ⊤) ((Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechComplex π M U).homology n)] :
    letI := BaseCechBridge.baseCohomologyModule π M n
    Module.Finite Γ(S, ⊤) (AffineH.Projective.H M n) := by
  cases n with
  | zero =>
      let := BaseCechBridge.baseCohomologyModule π M 0
      let := BaseCechLinearBridge.nativeCechBaseModule π M U 0
      let : Module.Finite Γ(S, ⊤) ((CechScalars.Projective.moduleCechCohomologyFunctor U 0).obj M) :=
        Module.Finite.equiv (BaseCechLinearBridge.baseCechHomologyNativeLinearEquiv π M U 0)
      exact Module.Finite.of_injective (baseHZeroCechLinear π M U)
        (baseHZeroCechLinear_injective π M U hU)
  | succ n =>
      let := BaseCechBridge.baseCohomologyModule π M (n + 1)
      exact Module.Finite.equiv (BaseCechBridge.baseCechHomologyAffineHSuccLinearEquiv π M U hU hUaff n)

theorem baseCohomologyFinite_of_orderedBaseCech
    {X S : Scheme.{u}} [X.IsSeparated] (π : X ⟶ S)
    [IsNoetherianRing Γ(S, ⊤)] (M : X.Modules) [M.IsQuasicoherent]
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) (hU : IsOpenCover U)
    (hUaff : ∀ i, IsAffineOpen (U i)) (n : ℕ)
    [Module.Finite Γ(S, ⊤) ((OrderedBaseCech.Scheme.Modules.orderedBaseCechComplex π M U).homology n)] :
    letI := BaseCechBridge.baseCohomologyModule π M n
    Module.Finite Γ(S, ⊤) (AffineH.Projective.H M n) := by
  let : Module.Finite Γ(S, ⊤) ((Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechComplex π M U).homology n) :=
    BaseCechHomotopyEquiv.Scheme.Modules.baseCechComplex_homology_module_finite_of_orderedBaseCechComplex π M U n
  exact baseCohomologyFinite_of_baseCech π M U hU hUaff n

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.BaseFiniteness
