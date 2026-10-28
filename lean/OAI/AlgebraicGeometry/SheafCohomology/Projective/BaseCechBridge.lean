import OAI.AlgebraicGeometry.SheafCohomology.Projective.BaseCechLinearBridge
import OAI.AlgebraicGeometry.SheafCohomology.CechLinearComparison

/-! # Base Cech Bridge -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.BaseCechBridge

noncomputable section

/-! The affine-cover comparison with coefficients in the global functions of a base scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
universe u

@[instance_reducible]
def baseCohomologyModule {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules) (n : ℕ) :
    Module Γ(S, ⊤) (AffineH.Projective.H M n) := by
  letI := AffineH.Projective.globalSectionsCohomologyModule M n
  exact Module.compHom _ π.appTop.hom

def baseCechHomologyAffineHSuccLinearEquiv
    {X S : Scheme.{u}} [X.IsSeparated] (π : X ⟶ S)
    (M : X.Modules) [M.IsQuasicoherent]
    {ι : Type u} (U : ι → X.Opens) (hU : IsOpenCover U)
    (hUaff : ∀ i, IsAffineOpen (U i)) (n : ℕ) :
    letI := baseCohomologyModule π M (n + 1)
    (Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechComplex π M U).homology (n + 1) ≃ₗ[Γ(S, ⊤)]
      AffineH.Projective.H M (n + 1) := by
  letI := CechScalars.Projective.cechGlobalFunctionsModule M U (n + 1)
  letI := AffineH.Projective.globalSectionsCohomologyModule M (n + 1)
  letI := BaseCechLinearBridge.nativeCechBaseModule π M U (n + 1)
  letI := baseCohomologyModule π M (n + 1)
  let e := BaseCechLinearBridge.baseCechHomologyNativeLinearEquiv π M U (n + 1)
  let f := CechLinearComparison.Projective.affineCoverCechHSuccLinearEquiv M U hU hUaff n
  refine { e.toAddEquiv.trans f.toAddEquiv with map_smul' := ?_ }
  intro r x
  change f (e (r • x)) = _
  rw [e.map_smul]
  exact f.map_smul (π.appTop r) (e x)

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.BaseCechBridge
