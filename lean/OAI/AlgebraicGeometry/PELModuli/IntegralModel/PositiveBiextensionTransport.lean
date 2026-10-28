import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polarization.BaseChange

/-! # Positive Biextension Transport -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.PositiveBiextensionTransport

noncomputable section

/-! Actual ample line witnesses for a normalized polarization formula
transport through an isomorphism of the underlying group scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polarization.BaseChange
universe u
variable {K : Type u} [Field K]

def PositiveBiextension (X : Over (Spec (.of K))) [GrpObj X]
    (Q : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (X ⊗ X).left) : Prop :=
  ∃ L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X.left, L.IsAmple ∧
    Nonempty ((L.pullback η[X].left).sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule (Spec (.of K))) ∧
    Nonempty (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule Q.sheaf ((L.pullback (fst X X).left).sheaf))
      ((L.pullback (snd X X).left).sheaf) ≅ (L.pullback μ[X].left).sheaf)

def lineBundleCommutingPullbacks {W X Y Z : Scheme.{u}}
    (a : X ⟶ Y) (b : Y ⟶ Z) (c : X ⟶ W) (d : W ⟶ Z)
    (h : a ≫ b = c ≫ d) (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle Z) :
    ((L.pullback b).pullback a).sheaf ≅ ((L.pullback d).pullback c).sheaf :=
  (Scheme.Modules.pullbackComp a b).app L.sheaf ≪≫
    (Scheme.Modules.pullbackCongr h).app L.sheaf ≪≫
      (Scheme.Modules.pullbackComp c d).symm.app L.sheaf

theorem positiveBiextension_of_iso {X Y : Over (Spec (.of K))} [GrpObj X] [GrpObj Y]
    (e : X ≅ Y) [IsMonHom e.hom] (QX : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (X ⊗ X).left) (QY : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (Y ⊗ Y).left)
    (he : QY.sheaf ≅ (QX.pullback (e.inv ⊗ₘ e.inv).left).sheaf)
    (h : PositiveBiextension X QX) : PositiveBiextension Y QY := by
  obtain ⟨L, hL, ⟨hZero⟩, ⟨hFormula⟩⟩ := h
  have : IsIso e.inv.left := inferInstanceAs (IsIso (((Over.forget _).mapIso e).inv))
  let a₂ := (e.inv ⊗ₘ e.inv).left
  have : IsIso a₂ := inferInstanceAs
    (IsIso ((Over.forget (Spec (.of K))).map (e.inv ⊗ₘ e.inv)))
  let L' := L.pullback e.inv.left
  refine ⟨L', hL.pullback_of_isIso e.inv.left, ⟨?_⟩, ⟨?_⟩⟩
  · exact (Scheme.Modules.pullbackComp η[Y].left e.inv.left).app L.sheaf ≪≫
      (Scheme.Modules.pullbackCongr (congrArg Over.Hom.left (IsMonHom.one_hom e.inv))).app L.sheaf ≪≫ hZero
  · let Q₁ := (L.pullback (fst X X).left).sheaf
    let Q₂ := (L.pullback (snd X X).left).sheaf
    let e₁ : (L'.pullback (fst Y Y).left).sheaf ≅ (Scheme.Modules.pullback a₂).obj Q₁ :=
      lineBundleCommutingPullbacks (fst Y Y).left e.inv.left a₂ (fst X X).left
        (Over.tensorHom_left_fst _ _ _ _).symm L
    let e₂ : (L'.pullback (snd Y Y).left).sheaf ≅ (Scheme.Modules.pullback a₂).obj Q₂ :=
      lineBundleCommutingPullbacks (snd Y Y).left e.inv.left a₂ (snd X X).left
        (Over.tensorHom_left_snd _ _ _ _).symm L
    exact AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleCongr
      (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleCongr he e₁ ≪≫ (AbelianModuli.HilbertConstruction.Tensor.ProductBaseChange.tensorModulePullbackIso a₂ QX.sheaf Q₁).symm) e₂ ≪≫
      (AbelianModuli.HilbertConstruction.Tensor.ProductBaseChange.tensorModulePullbackIso a₂ (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule QX.sheaf Q₁) Q₂).symm ≪≫
      (Scheme.Modules.pullback a₂).mapIso hFormula ≪≫
      lineBundleCommutingPullbacks a₂ μ[X].left μ[Y].left e.inv.left
        (congrArg Over.Hom.left (IsMonHom.mul_hom e.inv)).symm L

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.PositiveBiextensionTransport
