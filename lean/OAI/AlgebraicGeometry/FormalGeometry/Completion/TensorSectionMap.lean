import OAI.AlgebraicGeometry.SheafCohomology.Projective.GlobalTensorSectionCoherence
import OAI.AlgebraicGeometry.SheafCohomology.Projective.TensorSectionBilinear
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Global.Sections

/-! # Tensor Section Map -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.TensorSectionMap

noncomputable section

/-! Tensoring by an actual section, and its global coefficient in a specified frame. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory MonoidalCategory Opposite OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Global.Sections

namespace Construction

universe u

attribute [local instance] SheafCohomology.Projective.Monoidal.Scheme.Modules.monoidalCategory

def structureLeftUnitor {X : Scheme.{u}} (M : X.Modules) :
    AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⊗ M ≅ M :=
  ((SheafCohomology.Projective.TensorSections.monoidalUnitObjIso X).symm ⊗ᵢ Iso.refl M) ≪≫ λ_ M

theorem structureLeftUnitor_tensorSection_top {X : Scheme.{u}} (M : X.Modules)
    (r : Γ(X, ⊤)) (x : Γ(M, ⊤)) :
    (structureLeftUnitor M).hom.val.app (op ⊤) (SheafCohomology.Projective.TensorSections.tensorSection (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X) M ⊤ r x) = r • x := by
  have h1 : (structureLeftUnitor M).hom.val.app (op ⊤)
      (SheafCohomology.Projective.TensorSections.tensorSection (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X) M ⊤ (1 : Γ(X, ⊤)) x) = x := by
    change (λ_ M).hom.val.app (op ⊤)
      (((SheafCohomology.Projective.TensorSections.monoidalUnitObjIso X).inv ⊗ₘ 𝟙 M).val.app (op ⊤)
        (SheafCohomology.Projective.TensorSections.tensorSection (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X) M ⊤ (1 : Γ(X, ⊤)) x)) = x
    exact (congrArg ((λ_ M).hom.val.app (op ⊤))
      (SheafCohomology.Projective.TensorFrameSections.tensorSection_map (SheafCohomology.Projective.TensorSections.monoidalUnitObjIso X).inv (𝟙 M) ⊤ (1 : Γ(X, ⊤)) x)).trans
        (SheafCohomology.Projective.GlobalTensorSectionCoherence.leftUnitor_tensorSection_top M x)
  have hr : (r : Γ(AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X, ⊤)) = r • (1 : Γ(X, ⊤)) := (mul_one r).symm
  calc
    _ = (structureLeftUnitor M).hom.val.app (op ⊤)
        (SheafCohomology.Projective.TensorSections.tensorSection (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X) M ⊤ (r • (1 : Γ(X, ⊤))) x) :=
      congrArg (fun t => (structureLeftUnitor M).hom.val.app (op ⊤)
        (SheafCohomology.Projective.TensorSections.tensorSection (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X) M ⊤ t x)) hr
    _ = _ := by rw [SheafCohomology.Projective.TensorSectionBilinear.tensorSection_smul_left, map_smul, h1]

def tensorSectionMap {X : Scheme.{u}} {P : X.Modules}
    (s : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶ P) (M : X.Modules) : M ⟶ P ⊗ M :=
  (structureLeftUnitor M).inv ≫ (s ⊗ₘ 𝟙 M)

theorem tensorSectionMap_top {X : Scheme.{u}} {P : X.Modules}
    (s : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶ P) (M : X.Modules) (x : Γ(M, ⊤)) :
    (tensorSectionMap s M).app ⊤ x =
      SheafCohomology.Projective.TensorSections.tensorSection P M ⊤ (s.app ⊤ (1 : Γ(X, ⊤))) x := by
  have h := congrArg ((structureLeftUnitor M).inv.app ⊤)
    (structureLeftUnitor_tensorSection_top M 1 x)
  rw [one_smul] at h
  have hi : (structureLeftUnitor M).inv.app ⊤ x =
      SheafCohomology.Projective.TensorSections.tensorSection (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X) M ⊤ (1 : Γ(X, ⊤)) x := by
    exact h.symm.trans (SheafCohomology.Projective.SectionIdentities.Scheme.Modules.iso_inv_hom_app_applyT
      (structureLeftUnitor M).symm (op ⊤) _)
  change (s ⊗ₘ 𝟙 M).val.app (op ⊤) ((structureLeftUnitor M).inv.app ⊤ x) = _
  rw [hi]
  exact SheafCohomology.Projective.TensorFrameSections.tensorSection_map s (𝟙 M) ⊤ (1 : Γ(X, ⊤)) x

theorem tensorSectionMap_globalSections_injective_of_frame
    {X : Scheme.{u}} {P : X.Modules} (s : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶ P) (M : X.Modules)
    (e : P ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X)
    (hr : Function.Injective (fun x : Γ(M, ⊤) =>
      (show Γ(X, ⊤) from (s ≫ e.hom).app ⊤ (1 : Γ(X, ⊤))) • x)) :
    Function.Injective ((tensorSectionMap s M).app ⊤) := by
  let d : P ⊗ M ≅ M := (e ⊗ᵢ Iso.refl M) ≪≫ structureLeftUnitor M
  have hd (x : Γ(M, ⊤)) :
      d.hom.app ⊤ ((tensorSectionMap s M).app ⊤ x) =
        (show Γ(X, ⊤) from (s ≫ e.hom).app ⊤ (1 : Γ(X, ⊤))) • x := by
    rw [tensorSectionMap_top]
    change (structureLeftUnitor M).hom.val.app (op ⊤)
      ((e.hom ⊗ₘ 𝟙 M).val.app (op ⊤) (SheafCohomology.Projective.TensorSections.tensorSection P M ⊤ _ x)) = _
    rw [SheafCohomology.Projective.TensorFrameSections.tensorSection_map]
    exact structureLeftUnitor_tensorSection_top M _ x
  intro x y h
  apply hr
  exact (hd x).symm.trans ((congrArg (d.hom.app ⊤) h).trans (hd y))

end Construction

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.TensorSectionMap
