import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coefficient.GlobalSectionsFunctor

/-! # Module Section Identity -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Global.ModuleSectionIdentity

noncomputable section

/-! The global coefficient-presheaf module identifies with the native module of global sections. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

variable {X : Scheme.{u}}

def globalModuleSectionsIdentity (M : X.Modules) :
    (RingModulePresheaf.globalRingModulePresheaf M).obj (.op ⊤) ≃ₗ[Γ(X, ⊤)] Γ(M, ⊤) := by
  let e : (RingModulePresheaf.globalRingModulePresheaf M).obj (.op ⊤) ≅ ModuleCat.of Γ(X, ⊤) Γ(M, ⊤) := by
    refine ModuleCat.isoMk (Iso.refl _) ?_
    intro r
    ext (x : Γ(M, ⊤))
    change r • x = X.presheaf.map
      ((initialOpOfTerminal isTerminalTop).to (.op (⊤ : X.Opens))) r • x
    rw [Subsingleton.elim ((initialOpOfTerminal isTerminalTop).to (.op (⊤ : X.Opens))) (𝟙 _)]
    simp
  exact e.toLinearEquiv

def coefficientGlobalSectionsNativeIso {R : Type u} [CommRing R]
    (c : R →+* Γ(X, ⊤)) (M : X.Modules) :
    (Coefficient.GlobalSectionsFunctor.coefficientGlobalSectionsFunctor c).obj M ≃ₗ[R]
      (ModuleCat.restrictScalars c).obj (ModuleCat.of Γ(X, ⊤) Γ(M, ⊤)) :=
  ((ModuleCat.restrictScalars c).mapIso (globalModuleSectionsIdentity M).toModuleIso).toLinearEquiv

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Global.ModuleSectionIdentity
