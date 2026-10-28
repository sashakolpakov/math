import OAI.AlgebraicGeometry.AbelianScheme.CentralAction.LinePullbackFormula
import OAI.AlgebraicGeometry.AbelianScheme.CentralAction.FunctionDescent
import OAI.AlgebraicGeometry.AbelianScheme.CentralAction.FramedLineIso

/-! # Pull Hom Scalars -/

namespace OAI.AlgebraicGeometry.AbelianScheme.CentralAction.PullHomScalars

noncomputable section

/-! Intrinsic scalar coordinates of line-bundle endomorphisms respect
native descent comparisons, without any choice of pullback frames. -/

set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat

namespace Construction

universe u
variable {S : Scheme.{u}} {X T W : Over S}

theorem linePullHom_comp (f : T ⟶ X) (g : W ⟶ T) (f' : W ⟶ X) (hf : g ≫ f = f')
    {L M N : X.left.Modules}
    (a : (Scheme.Modules.pullback f.left).obj L ⟶ (Scheme.Modules.pullback f.left).obj M)
    (b : (Scheme.Modules.pullback f.left).obj M ⟶ (Scheme.Modules.pullback f.left).obj N) :
    pullHom (F := LinePullHom.Construction.overSchemeModulePullbacks S) (a ≫ b) g f' f' hf hf =
      pullHom (F := LinePullHom.Construction.overSchemeModulePullbacks S) a g f' f' hf hf ≫
        pullHom (F := LinePullHom.Construction.overSchemeModulePullbacks S) b g f' f' hf hf := by
  rw [LinePullbackFormula.Construction.linePullHom_formula, LinePullbackFormula.Construction.linePullHom_formula, LinePullbackFormula.Construction.linePullHom_formula]
  let e := LinePullbackFormula.Construction.linePullbackSquareIso f g f' hf
  let G := Scheme.Modules.pullback g.left
  change e.inv.app L ≫ G.map (a ≫ b) ≫ e.hom.app N =
    (e.inv.app L ≫ G.map a ≫ e.hom.app M) ≫
      e.inv.app M ≫ G.map b ≫ e.hom.app N
  simp only [Functor.map_comp, Category.assoc, Iso.hom_inv_id_app_assoc]

theorem linePullHom_map (f : T ⟶ X) (g : W ⟶ T) (f' : W ⟶ X) (hf : g ≫ f = f')
    {L M : X.left.Modules} (b : L ⟶ M) :
    pullHom (F := LinePullHom.Construction.overSchemeModulePullbacks S)
      ((Scheme.Modules.pullback f.left).map b) g f' f' hf hf =
        (Scheme.Modules.pullback f'.left).map b := by
  rw [LinePullbackFormula.Construction.linePullHom_formula]
  let e := LinePullbackFormula.Construction.linePullbackSquareIso f g f' hf
  have h := e.hom.naturality b
  change (Scheme.Modules.pullback g.left).map ((Scheme.Modules.pullback f.left).map b) ≫
      e.hom.app M = e.hom.app L ≫ (Scheme.Modules.pullback f'.left).map b at h
  change e.inv.app L ≫ _ ≫ e.hom.app M = _
  rw [h, Iso.inv_hom_id_app_assoc]

theorem linePullHom_scalar (f : T ⟶ X) (g : W ⟶ T) (f' : W ⟶ X) (hf : g ≫ f = f')
    (L : X.left.Modules) (r : Γ(T.left, ⊤)) :
    pullHom (F := LinePullHom.Construction.overSchemeModulePullbacks S)
      (Quotients.FiniteDescent.ModuleScalarsApp.Construction.ModuleScalars.scalar ((Scheme.Modules.pullback f.left).obj L) r) g f' f' hf hf =
        Quotients.FiniteDescent.ModuleScalarsApp.Construction.ModuleScalars.scalar ((Scheme.Modules.pullback f'.left).obj L) (g.left.appTop r) := by
  rw [LinePullbackFormula.Construction.linePullHom_formula, Quotients.FiniteDescent.ModuleScalarsApp.Construction.ModuleScalars.pullback_scalar]
  let e := LinePullbackFormula.Construction.linePullbackSquareIso f g f' hf
  change e.inv.app L ≫ Quotients.FiniteDescent.ModuleScalarsApp.Construction.ModuleScalars.scalar _ (g.left.appTop r) ≫ e.hom.app L = _
  rw [Quotients.FiniteDescent.ModuleScalarsApp.Construction.ModuleScalars.scalar_naturality, Iso.inv_hom_id_app_assoc]

theorem lineBundleEndRingEquiv_pullHom
    (f : T ⟶ X) (g : W ⟶ T) (f' : W ⟶ X) (hf : g ≫ f = f')
    (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X.left) (a : End (L.pullback f.left).sheaf) :
    LineEndRigidity.Construction.lineBundleEndRingEquiv (L.pullback f'.left)
        (pullHom (F := LinePullHom.Construction.overSchemeModulePullbacks S) a g f' f' hf hf) =
      g.left.appTop (LineEndRigidity.Construction.lineBundleEndRingEquiv (L.pullback f.left) a) := by
  conv_lhs => rw [← LineEndRigidity.Construction.scalar_lineBundleEndRingEquiv (L.pullback f.left) a]
  erw [linePullHom_scalar]
  exact LineEndRigidity.Construction.lineBundleEndRingEquiv_scalar (L.pullback f'.left) _

theorem line_comparison_scalar_invariant
    (f : T ⟶ X) (L M : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X.left) (b : L.sheaf ≅ M.sheaf)
    (a : (L.pullback f.left).sheaf ≅ (M.pullback f.left).sheaf)
    (p q : W ⟶ T) (hpq : p ≫ f = q ≫ f)
    (ha : pullHom (F := LinePullHom.Construction.overSchemeModulePullbacks S) a.hom p (p ≫ f) (p ≫ f) rfl rfl =
      pullHom (F := LinePullHom.Construction.overSchemeModulePullbacks S) a.hom q (p ≫ f) (p ≫ f) hpq.symm hpq.symm) :
    p.left.appTop (LineEndRigidity.Construction.lineBundleEndRingEquiv (L.pullback f.left)
      (a.hom ≫ (Scheme.Modules.pullback f.left).map b.inv)) =
    q.left.appTop (LineEndRigidity.Construction.lineBundleEndRingEquiv (L.pullback f.left)
      (a.hom ≫ (Scheme.Modules.pullback f.left).map b.inv)) := by
  let c : End (L.pullback f.left).sheaf := a.hom ≫ (Scheme.Modules.pullback f.left).map b.inv
  have he : pullHom (F := LinePullHom.Construction.overSchemeModulePullbacks S) c p (p ≫ f) (p ≫ f) rfl rfl =
      pullHom (F := LinePullHom.Construction.overSchemeModulePullbacks S) c q (p ≫ f) (p ≫ f) hpq.symm hpq.symm := by
    calc
      _ = pullHom (F := LinePullHom.Construction.overSchemeModulePullbacks S) a.hom p (p ≫ f) (p ≫ f) rfl rfl ≫
          (Scheme.Modules.pullback (p ≫ f).left).map b.inv := by
        exact (linePullHom_comp f p (p ≫ f) rfl a.hom
          ((Scheme.Modules.pullback f.left).map b.inv)).trans
            (congrArg (_ ≫ ·) (linePullHom_map f p (p ≫ f) rfl b.inv))
      _ = pullHom (F := LinePullHom.Construction.overSchemeModulePullbacks S) a.hom q (p ≫ f) (p ≫ f) hpq.symm hpq.symm ≫
          (Scheme.Modules.pullback (p ≫ f).left).map b.inv := congrArg (· ≫ _) ha
      _ = _ := by
        exact ((linePullHom_comp f q (p ≫ f) hpq.symm a.hom
          ((Scheme.Modules.pullback f.left).map b.inv)).trans
            (congrArg (_ ≫ ·) (linePullHom_map f q (p ≫ f) hpq.symm b.inv))).symm
  exact (lineBundleEndRingEquiv_pullHom f p (p ≫ f) rfl L c).symm.trans
    ((congrArg (LineEndRigidity.Construction.lineBundleEndRingEquiv (L.pullback (p ≫ f).left)) he).trans
      (lineBundleEndRingEquiv_pullHom f q (p ≫ f) hpq.symm L c))

end Construction

end

end OAI.AlgebraicGeometry.AbelianScheme.CentralAction.PullHomScalars
