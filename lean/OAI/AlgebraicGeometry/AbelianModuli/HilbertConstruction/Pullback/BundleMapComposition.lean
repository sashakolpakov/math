import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles

/-! # Bundle Map Composition -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Pullback.BundleMapComposition

noncomputable section

/-! Pullback of a map between pulled-back bundles, with the composition isomorphisms explicit. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X Y Z : Scheme.{u}}

def pullbackBundleMapComp (a : Z ⟶ Y) (f : Y ⟶ X) {L M : Line.Bundles.LineBundle X}
    (φ : (L.pullback f).sheaf ⟶ (M.pullback f).sheaf) :
    (L.pullback (a ≫ f)).sheaf ⟶ (M.pullback (a ≫ f)).sheaf :=
  (Scheme.Modules.pullbackComp a f).inv.app L.sheaf ≫
    (Scheme.Modules.pullback a).map φ ≫ (Scheme.Modules.pullbackComp a f).hom.app M.sheaf

theorem pullbackBundleMapComp_of_pullback (a : Z ⟶ Y) (f : Y ⟶ X) {L M : Line.Bundles.LineBundle X}
    (φ : L.sheaf ⟶ M.sheaf) :
    pullbackBundleMapComp a f ((Scheme.Modules.pullback f).map φ) =
      (Scheme.Modules.pullback (a ≫ f)).map φ := by
  have hn : (Scheme.Modules.pullback a).map ((Scheme.Modules.pullback f).map φ) ≫
      (Scheme.Modules.pullbackComp a f).hom.app M.sheaf =
    (Scheme.Modules.pullbackComp a f).hom.app L.sheaf ≫
      (Scheme.Modules.pullback (a ≫ f)).map φ :=
    (Scheme.Modules.pullbackComp a f).hom.naturality φ
  exact (congrArg (fun k => (Scheme.Modules.pullbackComp a f).inv.app L.sheaf ≫ k) hn).trans
    ((Scheme.Modules.pullbackComp a f).inv_hom_id_app_assoc L.sheaf _)

theorem pullbackBundleMapComp_comp (a : Z ⟶ Y) (f : Y ⟶ X) {L M N : Line.Bundles.LineBundle X}
    (φ : (L.pullback f).sheaf ⟶ (M.pullback f).sheaf)
    (ψ : (M.pullback f).sheaf ⟶ (N.pullback f).sheaf) :
    pullbackBundleMapComp a f (φ ≫ ψ) = pullbackBundleMapComp a f φ ≫ pullbackBundleMapComp a f ψ := by
  change (Scheme.Modules.pullback f).obj L.sheaf ⟶ (Scheme.Modules.pullback f).obj M.sheaf at φ
  change (Scheme.Modules.pullback f).obj M.sheaf ⟶ (Scheme.Modules.pullback f).obj N.sheaf at ψ
  let F := Scheme.Modules.pullback a
  let cL := (Scheme.Modules.pullbackComp a f).app L.sheaf
  let cM := (Scheme.Modules.pullbackComp a f).app M.sheaf
  let cN := (Scheme.Modules.pullbackComp a f).app N.sheaf
  have h : cL.inv ≫ F.map (φ ≫ ψ) ≫ cN.hom =
      (cL.inv ≫ F.map φ ≫ cM.hom) ≫ (cM.inv ≫ F.map ψ ≫ cN.hom) := by
    rw [F.map_comp]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
  exact h

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Pullback.BundleMapComposition
