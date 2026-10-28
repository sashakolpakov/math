import OAI.AlgebraicGeometry.Quotients.FiniteDescent.CubeRelativeSectionsPullback

/-! # Cube Relative Sections Naturality -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.CubeRelativeSectionsNaturality.Construction.CubeCech

noncomputable section

/-! Pullback of base-field module sections with a specified structural morphism. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

universe u

variable {k : Type u} [Field k] {X Y : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k)) (h : Y ⟶ X) (hh : h ≫ f = g)

def relativeSectionsMap (U : X.Opens) (V : Y.Opens) (hVU : V ≤ h ⁻¹ᵁ U) :
    (CubeRelativeModuleSheaf.Construction.CubeCech.structureSheafAsBaseFieldSheaf f).obj.obj (op U) →ₗ[k]
      (CubeRelativeModuleSheaf.Construction.CubeCech.structureSheafAsBaseFieldSheaf g).obj.obj (op V) :=
  (CubeRelativeSectionsPullback.Construction.CubeCech.relativeSectionsCongr hh V).toLinearMap.comp (CubeRelativeSectionsPullback.Construction.CubeCech.relativeSectionsPullback f h U V hVU)

theorem relativeSectionsMap_apply (U : X.Opens) (V : Y.Opens) (hVU : V ≤ h ⁻¹ᵁ U)
    (x : (CubeRelativeModuleSheaf.Construction.CubeCech.structureSheafAsBaseFieldSheaf f).obj.obj (op U)) :
    (relativeSectionsMap f g h hh U V hVU x : Γ(Y, V)) = h.appLE U V hVU x :=
  (CubeRelativeSectionsPullback.Construction.CubeCech.relativeSectionsCongr_apply hh V _).trans (CubeRelativeSectionsPullback.Construction.CubeCech.relativeSectionsPullback_apply f h U V hVU x)

theorem relativeSectionsMap_restrict {U U' : X.Opens} {V V' : Y.Opens}
    (i : U' ⟶ U) (j : V' ⟶ V) (hVU : V ≤ h ⁻¹ᵁ U) (hV'U' : V' ≤ h ⁻¹ᵁ U')
    (x : (CubeRelativeModuleSheaf.Construction.CubeCech.structureSheafAsBaseFieldSheaf f).obj.obj (op U)) :
    relativeSectionsMap f g h hh U' V' hV'U'
      ((CubeRelativeModuleSheaf.Construction.CubeCech.structureSheafAsBaseFieldSheaf f).obj.map i.op x) =
      (CubeRelativeModuleSheaf.Construction.CubeCech.structureSheafAsBaseFieldSheaf g).obj.map j.op
        (relativeSectionsMap f g h hh U V hVU x) := by
  have he : X.presheaf.map i.op ≫ h.appLE U' V' hV'U' =
      h.appLE U V hVU ≫ Y.presheaf.map j.op := by
    rw [Scheme.Hom.map_appLE, Scheme.Hom.appLE_map]
  exact (relativeSectionsMap_apply f g h hh U' V' hV'U' _).trans
    ((congrArg (fun q : Γ(X, U) ⟶ Γ(Y, V') ↦ q x) he).trans
      (congrArg (Y.presheaf.map j.op) (relativeSectionsMap_apply f g h hh U V hVU x).symm))

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.CubeRelativeSectionsNaturality.Construction.CubeCech
