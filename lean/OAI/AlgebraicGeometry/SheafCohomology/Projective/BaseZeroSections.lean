import OAI.AlgebraicGeometry.SheafCohomology.Projective.BaseCechAllDegrees

/-! # Base Zero Sections -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.BaseZeroSections

noncomputable section

/-! Global sections and degree-zero ordered Čech cohomology over the actual base ring. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
universe u

@[instance_reducible]
def baseGlobalSectionsModule {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules) :
    Module Γ(S, ⊤) Γ(M, ⊤) := Module.compHom Γ(M, ⊤) π.appTop.hom

def baseHZeroLinearEquivGlobalSections {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules) :
    letI := BaseCechBridge.baseCohomologyModule π M 0
    letI := baseGlobalSectionsModule π M
    AffineH.Projective.H M 0 ≃ₗ[Γ(S, ⊤)] Γ(M, ⊤) := by
  letI := AffineH.Projective.globalSectionsCohomologyModule M 0
  let e := AffineH.Projective.hZeroCanonicalLinearEquivGlobalSections M
  letI := BaseCechBridge.baseCohomologyModule π M 0
  letI := baseGlobalSectionsModule π M
  exact { e.toAddEquiv with map_smul' := fun r x => e.map_smul (π.appTop r) x }

def baseCechHZeroGlobalSectionsLinearEquiv {X S : Scheme.{u}} (π : X ⟶ S)
    (M : X.Modules) {ι : Type u} (U : ι → X.Opens) (hU : IsOpenCover U) :
    letI := baseGlobalSectionsModule π M
    (Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechComplex π M U).homology 0 ≃ₗ[Γ(S, ⊤)] Γ(M, ⊤) := by
  letI := BaseCechBridge.baseCohomologyModule π M 0
  letI := baseGlobalSectionsModule π M
  letI := BaseCechLinearBridge.nativeCechBaseModule π M U 0
  exact (BaseCechLinearBridge.baseCechHomologyNativeLinearEquiv π M U 0).trans
    ((LinearEquiv.ofBijective (BaseFiniteness.baseHZeroCechLinear π M U)
      ⟨BaseFiniteness.baseHZeroCechLinear_injective π M U hU, BaseCechAllDegrees.baseHZeroCechLinear_surjective π M U hU⟩).symm.trans
      (baseHZeroLinearEquivGlobalSections π M))

def orderedBaseCechHZeroGlobalSectionsLinearEquiv {X S : Scheme.{u}} (π : X ⟶ S)
    (M : X.Modules) {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) (hU : IsOpenCover U) :
    letI := baseGlobalSectionsModule π M
    (OrderedBaseCech.Scheme.Modules.orderedBaseCechComplex π M U).homology 0 ≃ₗ[Γ(S, ⊤)] Γ(M, ⊤) := by
  letI := baseGlobalSectionsModule π M
  exact (BaseCechHomotopyEquiv.Scheme.Modules.baseCechOrderedHomologyIso π M U 0).symm.toLinearEquiv.trans
    (baseCechHZeroGlobalSectionsLinearEquiv π M U hU)

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.BaseZeroSections
