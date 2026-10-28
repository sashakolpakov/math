import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coefficient.PullbackSectionValues

/-! # Pullback Section To Open -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coefficient.PullbackSectionToOpen

noncomputable section

/-! Pull a section back and restrict it to a specified smaller open, with its original coefficient action. This operation is natural in both opens. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
universe u

variable {X Y : Scheme.{u}} {R : Type u} [CommRing R]
variable (f : X ⟶ Y) (cY : R →+* Γ(Y, ⊤)) (cX : R →+* Γ(X, ⊤))
variable (hc : f.appTop.hom.comp cY = cX) (M : Y.Modules)

def coefficientPullbackSectionToOpen (U : Y.Opens) (W : X.Opens) (hW : W ≤ f ⁻¹ᵁ U) :
    (ModulePresheaf.coefficientModulePresheaf cY M).obj (op U) →ₗ[R]
      (ModulePresheaf.coefficientModulePresheaf cX ((Scheme.Modules.pullback f).obj M)).obj (op W) := by
  subst cX
  exact ((ModulePresheaf.coefficientModulePresheaf (f.appTop.hom.comp cY) ((Scheme.Modules.pullback f).obj M)).map
      (homOfLE hW).op).hom.comp (PullbackSectionValues.coefficientPullbackSectionValueMap f cY M U)

theorem coefficientPullbackSectionToOpen_apply (U : Y.Opens) (W : X.Opens)
    (hW : W ≤ f ⁻¹ᵁ U) (x : (ModulePresheaf.coefficientModulePresheaf cY M).obj (op U)) :
    coefficientPullbackSectionToOpen f cY cX hc M U W hW x =
      ((Scheme.Modules.pullback f).obj M).presheaf.map (homOfLE hW).op
        (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M).app U x) := by
  subst cX
  rfl

theorem coefficientPullbackSectionToOpen_naturality
    {U U' : Y.Opens} {W W' : X.Opens}
    (hW : W ≤ f ⁻¹ᵁ U) (hW' : W' ≤ f ⁻¹ᵁ U')
    (hiU : U' ≤ U) (hiW : W' ≤ W)
    (x : (ModulePresheaf.coefficientModulePresheaf cY M).obj (op U)) :
    coefficientPullbackSectionToOpen f cY cX hc M U' W' hW'
        ((ModulePresheaf.coefficientModulePresheaf cY M).map (homOfLE hiU).op x) =
      (ModulePresheaf.coefficientModulePresheaf cX ((Scheme.Modules.pullback f).obj M)).map (homOfLE hiW).op
        (coefficientPullbackSectionToOpen f cY cX hc M U W hW x) := by
  rw [coefficientPullbackSectionToOpen_apply, coefficientPullbackSectionToOpen_apply]
  change Γ(M, U) at x
  let N := (Scheme.Modules.pullback f).obj M
  let u : M ⟶ (Scheme.Modules.pushforward f).obj N :=
    (Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M
  let t : Γ(N, (TopologicalSpace.Opens.map f.base).obj U) := u.app U x
  have hn := ConcreteCategory.congr_hom (u.mapPresheaf.naturality (homOfLE hiU).op) x
  change u.app U' (M.presheaf.map (homOfLE hiU).op x) =
    N.presheaf.map ((TopologicalSpace.Opens.map f.base).map (homOfLE hiU)).op t at hn
  change N.presheaf.map (homOfLE hW').op
      (u.app U' (M.presheaf.map (homOfLE hiU).op x)) =
    N.presheaf.map (homOfLE hiW).op (N.presheaf.map (homOfLE hW).op t)
  rw [hn, ← N.presheaf.map_comp_apply, ← N.presheaf.map_comp_apply]
  exact ConcreteCategory.congr_hom (N.presheaf.congr_map (Subsingleton.elim _ _)) t

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coefficient.PullbackSectionToOpen
