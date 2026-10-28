import OAI.AlgebraicGeometry.Comparison.Betti.TopologicalSheafPullback
import OAI.AlgebraicGeometry.Comparison.Betti.SingularPresheafPullback

/-! # Constant Pullback Normalization -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.ConstantPullbackNormalization

noncomputable section

/-! Actual constant functions normalize the coefficient identifications used by pullback. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite

variable (M : TopCat.{0})

theorem constantLocallyConstant_homEquiv :
    (constantSheafAdj (Opens.grothendieckTopology M) (ModuleCat.{0} ℂ) isTerminalTop).homEquiv
        (ModuleCat.of ℂ ℂ) (AlgebraicTopology.DeRham.Comparison.LocallyConstantSheaf.locallyConstantSheaf M)
        (Analysis.DifferentialForms.Manifold.DeRhamResolution.constantComplexLocallyConstantIsoOn M).hom =
      ModuleCat.ofHom (LocallyConstant.constₗ (X := (⊤ : Opens M)) ℂ) := by
  let a := constantPresheafAdj (ModuleCat.{0} ℂ) (show IsTerminal (⊤ : Opens M) from isTerminalTop)
  let b := sheafificationAdjunction (Opens.grothendieckTopology M) (ModuleCat.{0} ℂ)
  have hb : b.homEquiv (AlgebraicTopology.DeRham.Comparison.ConstantLocallyConstant.constantComplexPresheaf M) (AlgebraicTopology.DeRham.Comparison.LocallyConstantSheaf.locallyConstantSheaf M)
      (Analysis.DifferentialForms.Manifold.DeRhamResolution.constantComplexLocallyConstantIsoOn M).hom = AlgebraicTopology.DeRham.Comparison.ConstantLocallyConstant.constantToLocallyConstant M :=
    AlgebraicTopology.DeRham.Comparison.ConstantLocallyConstant.constantSheafLocallyConstantIso_fac M
  change (a.comp b).homEquiv _ _ _ = _
  rw [Adjunction.comp_homEquiv]
  change a.homEquiv _ _ (b.homEquiv _ _ _) = _
  erw [hb]
  erw [Adjunction.homEquiv_unit]
  rfl

variable {M} {N : TopCat.{0}} (f : M ⟶ N)

def locallyConstantDirectImage : (AlgebraicTopology.DeRham.Comparison.LocallyConstantSheaf.locallyConstantSheaf N : ConstantSheafSections.ComplexSheaves N) ⟶
    (TopologicalSheafPullback.sheafDirectImage f).obj (AlgebraicTopology.DeRham.Comparison.LocallyConstantSheaf.locallyConstantSheaf M) where
  hom :=
    { app := fun U => ModuleCat.ofHom (LocallyConstant.comapₗ ℂ (SingularPresheafPullback.openPreimageMap f U.unop).hom)
      naturality := fun _U _V _i => by
        ext a
        rfl }

theorem constantPullbackIso_homEquiv (F : ConstantSheafSections.ComplexSheaves M)
    (g : ConstantSheafSections.standardConstantSheaf M ⟶ F) :
    (constantSheafAdj (Opens.grothendieckTopology N) (ModuleCat.{0} ℂ) isTerminalTop).homEquiv
        (ModuleCat.of ℂ ℂ) ((TopologicalSheafPullback.sheafDirectImage f).obj F)
        ((TopologicalSheafPullback.sheafImageAdjunction f).homEquiv _ _ ((TopologicalSheafPullback.constantPullbackIso f).hom ≫ g)) =
      (constantSheafAdj (Opens.grothendieckTopology M) (ModuleCat.{0} ℂ) isTerminalTop).homEquiv
        (ModuleCat.of ℂ ℂ) F g := by
  let a := constantSheafAdj (Opens.grothendieckTopology N) (ModuleCat.{0} ℂ) isTerminalTop
  let b := TopologicalSheafPullback.sheafImageAdjunction f
  let c := constantSheafAdj (Opens.grothendieckTopology M) (ModuleCat.{0} ℂ) isTerminalTop
  change (a.comp b).homEquiv _ _ ((TopologicalSheafPullback.constantPullbackIso f).hom ≫ g) = c.homEquiv _ _ g
  rw [Adjunction.homEquiv_naturality_right]
  have h : (a.comp b).homEquiv _ _ (TopologicalSheafPullback.constantPullbackIso f).hom = c.unit.app (ModuleCat.of ℂ ℂ) :=
    Adjunction.homEquiv_leftAdjointUniq_hom_app (a.comp b) c (ModuleCat.of ℂ ℂ)
  rw [h, Adjunction.homEquiv_unit]
  rfl

theorem locallyConstantPullbackIso_homEquiv :
    (TopologicalSheafPullback.sheafImageAdjunction f).homEquiv _ _ (TopologicalSheafPullback.locallyConstantPullbackIso f).hom =
      locallyConstantDirectImage f := by
  let eN : ConstantSheafSections.standardConstantSheaf N ≅ (AlgebraicTopology.DeRham.Comparison.LocallyConstantSheaf.locallyConstantSheaf N : ConstantSheafSections.ComplexSheaves N) :=
    Analysis.DifferentialForms.Manifold.DeRhamResolution.constantComplexLocallyConstantIsoOn N
  let eM : ConstantSheafSections.standardConstantSheaf M ≅ (AlgebraicTopology.DeRham.Comparison.LocallyConstantSheaf.locallyConstantSheaf M : ConstantSheafSections.ComplexSheaves M) :=
    Analysis.DifferentialForms.Manifold.DeRhamResolution.constantComplexLocallyConstantIsoOn M
  apply (Iso.cancel_iso_hom_left eN _ _).mp
  apply ((constantSheafAdj (Opens.grothendieckTopology N) (ModuleCat.{0} ℂ)
    isTerminalTop).homEquiv (ModuleCat.of ℂ ℂ) _).injective
  have he : (TopologicalSheafPullback.sheafInverseImage f).map eN.hom ≫ (TopologicalSheafPullback.locallyConstantPullbackIso f).hom =
      (TopologicalSheafPullback.constantPullbackIso f).hom ≫ eM.hom := by
    change (TopologicalSheafPullback.sheafInverseImage f).map eN.hom ≫
      ((TopologicalSheafPullback.sheafInverseImage f).map eN.inv ≫ (TopologicalSheafPullback.constantPullbackIso f).hom ≫ eM.hom) = _
    erw [← Category.assoc, ← Functor.map_comp, eN.hom_inv_id,
      (TopologicalSheafPullback.sheafInverseImage f).map_id, Category.id_comp]
  erw [← Adjunction.homEquiv_naturality_left, he]
  erw [constantPullbackIso_homEquiv]
  erw [constantLocallyConstant_homEquiv M]
  erw [(constantSheafAdj (Opens.grothendieckTopology N) (ModuleCat.{0} ℂ)
    isTerminalTop).homEquiv_naturality_right eN.hom (locallyConstantDirectImage f)]
  erw [constantLocallyConstant_homEquiv N]
  rfl

end

end OAI.AlgebraicGeometry.Comparison.Betti.ConstantPullbackNormalization
