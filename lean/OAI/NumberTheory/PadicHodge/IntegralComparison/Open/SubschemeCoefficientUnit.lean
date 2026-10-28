import OAI.NumberTheory.PadicHodge.IntegralComparison.Open.SubschemeSectionDiagram
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Global.ModuleScalars
import OAI.NumberTheory.PadicHodge.IntegralComparison.AffinePrincipal.Injective

/-! # Subscheme Coefficient Unit -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Open.SubschemeCoefficientUnit

noncomputable section

/-! The actual restriction unit is invertible on any diagram of opens
contained in the chosen open subscheme. A function on that subscheme
acts on its direct-image coefficient sheaf by genuine multiplication. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace Opposite _root_.HomologicalComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
variable {Y : Scheme.{u}} (V : Y.Opens) (N : Y.Modules)

abbrev extension := (Scheme.Modules.pushforward V.ι).obj (N.restrict V.ι)

def unit : N ⟶ extension V N := (Scheme.Modules.restrictAdjunction V.ι).unit.app N

def scalar (z : Γ(Y,V)) : extension V N ⟶ extension V N :=
  (Scheme.Modules.pushforward V.ι).map
    (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Global.ModuleScalars.globalModuleScalar (N.restrict V.ι)
      (V.ι.appLE V ⊤ V.ι_preimage_self.ge z))

def imageInclusion (U : Y.Opens) : V.ι ''ᵁ (V.ι ⁻¹ᵁ U) ⟶ V :=
  homOfLE (by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
    exact inf_le_left)

theorem scalar_app (z : Γ(Y,V)) (U : Y.Opens) (x : Γ(extension V N,U)) :
    (scalar V N z).app U x =
      Y.presheaf.map (imageInclusion V U).op z •
        (show Γ(N,V.ι ''ᵁ (V.ι ⁻¹ᵁ U)) from x) := by
  change (V.ι.appIso (V.ι ⁻¹ᵁ U)).inv
      (V.toScheme.presheaf.map (V.ι ⁻¹ᵁ U).leTop.op
        (V.ι.appLE V ⊤ V.ι_preimage_self.ge z)) •
      (show Γ(N,V.ι ''ᵁ (V.ι ⁻¹ᵁ U)) from x) = _
  have h := congrArg (fun a => a z)
    ((V.ι.appLE_map V.ι_preimage_self.ge (V.ι ⁻¹ᵁ U).leTop.op).trans
      (by rfl))
  have hring : (V.ι.appIso (V.ι ⁻¹ᵁ U)).inv
      (V.toScheme.presheaf.map (V.ι ⁻¹ᵁ U).leTop.op
        (V.ι.appLE V ⊤ V.ι_preimage_self.ge z)) =
      Y.presheaf.map (imageInclusion V U).op z := by
    have he := ConcreteCategory.congr_hom
      (V.ι.appLE_appIso_inv ((V.ι ⁻¹ᵁ U).leTop.le.trans V.ι_preimage_self.ge)) z
    exact (congrArg (V.ι.appIso (V.ι ⁻¹ᵁ U)).inv h).trans he
  rw [hring]

variable {C : Type v} [Category C] (F : C ⥤ Y.Opens)
  (hF : ∀ r, F.obj r ≤ V)

abbrev diagramMap := SubschemeSectionDiagram.coefficientMap F (SubschemeCoefficientUnit.unit V N)

include hF in
theorem diagramMap_isIso : IsIso (diagramMap V N F) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro r
  change IsIso (N.presheaf.map (homOfLE (V.ι.image_preimage_le (F.obj r.unop))).op)
  have he : homOfLE (V.ι.image_preimage_le (F.obj r.unop)) =
      eqToHom (SubschemeSectionDiagram.image_eq F V hF r.unop) := Subsingleton.elim _ _
  rw [he]
  infer_instance

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Open.SubschemeCoefficientUnit
