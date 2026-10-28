import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Canonical.DescentSquare
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.LineFramePullbackSquare
import OAI.AlgebraicGeometry.Picard.PoincareBundle.SquareRecoveryFormula

/-! # Line Frame Square Comparison -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.LineFrameSquareComparison.Construction

noncomputable section

/-! The concrete frame used for the Poincare parameter swap is exactly
the canonical frame of the corresponding square of descent covers. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem iso_inverse_frame_chain {C : Type*} [Category* C] {U V W X Y Z : C}
    (e : U ≅ V) (s : U ≅ W) (a : W ≅ X) (b : X ≅ Y) (c : Y ≅ Z) :
    (e.symm ≪≫ s ≪≫ a ≪≫ b ≪≫ c).symm = (a ≪≫ b ≪≫ c).symm ≪≫ (s.symm ≪≫ e) := by
  apply Iso.ext
  simp only [Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv, Category.assoc]

theorem nativeModuleDescentSquareIso_path {X Y X' Y' : Scheme.{u}}
    (f : X ⟶ Y) (f' : X' ⟶ Y') (s : Y' ⟶ Y) (t : X' ⟶ X)
    (w : t ≫ f = f' ≫ s) (L : Y.Modules) :
    Picard.Homomorphisms.ModuleHomBaseChange.Construction.moduleDescentSquareIso f f' s t w L =
      (Scheme.Modules.pullbackComp t f).app L ≪≫ (Scheme.Modules.pullbackCongr w).app L ≪≫
        ((Scheme.Modules.pullbackComp f' s).app L).symm := by
  rw [Picard.Homomorphisms.ModuleHomBaseChange.Construction.moduleDescentSquareIso_eq]
  have hc := congrArg (fun a => a.app L) (Picard.PoincareBundle.SquareRecoveryFormula.pullbackCongr_symm w)
  apply Iso.ext
  have hc' := congrArg Iso.hom hc
  change (Scheme.Modules.pullbackCongr w.symm).inv.app L = (Scheme.Modules.pullbackCongr w).hom.app L at hc'
  simp only [Picard.Homomorphisms.ModuleHomBaseChange.Construction.nativeModuleDescentSquareIso, NatIso.trans_app, Iso.trans_hom, Iso.symm_hom]
  exact congrArg (fun a => (Scheme.Modules.pullbackComp t f).hom.app L ≫ a ≫
    (Scheme.Modules.pullbackComp f' s).inv.app L) hc'

theorem lineFramePullbackSquare_eq_canonical {X Y : Scheme.{u}}
    (f : X ⟶ X) (g : Y ⟶ Y) (h : Y ⟶ X) (hs : g ≫ h = h ≫ f) (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X)
    (s : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ≅ (L.pullback f).sheaf) :
    (LineFramePullbackSquare.Construction.lineFramePullbackSquare f g h hs L s).symm = Canonical.DescentSquare.Construction.canonicalSquareFrame f g h h hs.symm L.sheaf s.symm := by
  unfold Canonical.DescentSquare.Construction.canonicalSquareFrame
  rw [nativeModuleDescentSquareIso_path]
  exact iso_inverse_frame_chain (AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso h) ((Scheme.Modules.pullback h).mapIso s)
    ((Scheme.Modules.pullbackComp h f).app L.sheaf) ((Scheme.Modules.pullbackCongr hs.symm).app L.sheaf)
    ((Scheme.Modules.pullbackComp g h).app L.sheaf).symm

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.LineFrameSquareComparison.Construction
