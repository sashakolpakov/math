import OAI.AlgebraicGeometry.Quotients.FiniteDescent.CubeSectionsAsAlgebra

/-! # Cube Relative Sections Pullback -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.CubeRelativeSectionsPullback.Construction.CubeCech

noncomputable section

/-! Linear pullback maps for regular functions viewed as base-field vector spaces. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

universe u

variable {k : Type u} [Field k] {X Y : Scheme.{u}}

def relativeSectionsPullback (f : X ⟶ Spec (.of k)) (h : Y ⟶ X)
    (U : X.Opens) (V : Y.Opens) (hVU : V ≤ h ⁻¹ᵁ U) :
    (CubeRelativeModuleSheaf.Construction.CubeCech.structureSheafAsBaseFieldSheaf f).obj.obj (op U) →ₗ[k]
      (CubeRelativeModuleSheaf.Construction.CubeCech.structureSheafAsBaseFieldSheaf (h ≫ f)).obj.obj (op V) :=
  (CubeSectionsAsAlgebra.Construction.CubeCech.sectionsAsBaseModuleIso (h ≫ f) V).toLinearEquiv.toLinearMap.comp
    ((CubeSectionsAsAlgebra.Construction.CubeCech.sectionsPullbackAlgHom f h U V hVU).toLinearMap.comp
      (CubeSectionsAsAlgebra.Construction.CubeCech.sectionsAsBaseModuleIso f U).toLinearEquiv.symm.toLinearMap)

theorem relativeSectionsPullback_apply (f : X ⟶ Spec (.of k)) (h : Y ⟶ X)
    (U : X.Opens) (V : Y.Opens) (hVU : V ≤ h ⁻¹ᵁ U)
    (x : (CubeRelativeModuleSheaf.Construction.CubeCech.structureSheafAsBaseFieldSheaf f).obj.obj (op U)) :
    relativeSectionsPullback f h U V hVU x = h.appLE U V hVU x := rfl

def relativeSectionsCongr {f g : X ⟶ Spec (.of k)} (h : f = g) (U : X.Opens) :
    (CubeRelativeModuleSheaf.Construction.CubeCech.structureSheafAsBaseFieldSheaf f).obj.obj (op U) ≃ₗ[k]
      (CubeRelativeModuleSheaf.Construction.CubeCech.structureSheafAsBaseFieldSheaf g).obj.obj (op U) := by
  subst g
  exact LinearEquiv.refl k _

theorem relativeSectionsCongr_apply {f g : X ⟶ Spec (.of k)} (h : f = g) (U : X.Opens)
    (x : (CubeRelativeModuleSheaf.Construction.CubeCech.structureSheafAsBaseFieldSheaf f).obj.obj (op U)) :
    (relativeSectionsCongr h U x : Γ(X, U)) = x := by
  subst g
  rfl

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.CubeRelativeSectionsPullback.Construction.CubeCech
