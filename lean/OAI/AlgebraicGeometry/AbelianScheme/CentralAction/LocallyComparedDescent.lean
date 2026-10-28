import OAI.AlgebraicGeometry.AbelianScheme.CentralAction.PullHomScalars

/-! # Locally Compared Descent -/

namespace OAI.AlgebraicGeometry.AbelianScheme.CentralAction.LocallyComparedDescent

noncomputable section

/-! On an open admitting a reference comparison, native compatibility
descends the actual isomorphism by descending its intrinsic scalar. -/

set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat

namespace Construction

theorem line_iso_desc_of_reference {S : Scheme.{0}} {X Y : Over S}
    (f : X ⟶ Y) [EffectiveEpi f.left] [Surjective f.left]
    (L M : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle Y.left) (b : L.sheaf ≅ M.sheaf) :
    let F := LinePullHom.Construction.overSchemeModulePullbacks S
    ∀ (a : (F.map f.op.toLoc).toFunctor.obj L.sheaf ≅
        (F.map f.op.toLoc).toFunctor.obj M.sheaf),
      (∀ (T : Over S) (p q : T ⟶ X) (hpq : p ≫ f = q ≫ f),
        pullHom (F := F) a.hom p (p ≫ f) (p ≫ f) rfl rfl =
          pullHom (F := F) a.hom q (p ≫ f) (p ≫ f) hpq.symm hpq.symm) →
      ∃ d : L.sheaf ≅ M.sheaf, (Scheme.Modules.pullback f.left).map d.hom = a.hom := by
  dsimp only
  intro a ha
  let c : End (L.pullback f.left).sheaf := a.hom ≫ (Scheme.Modules.pullback f.left).map b.inv
  have hc : IsIso c :=
    (a ≪≫ (Scheme.Modules.pullback f.left).mapIso b.symm).isIso_hom
  let r := LineEndRigidity.Construction.lineBundleEndRingEquiv (L.pullback f.left) c
  have hr {T : Scheme.{0}} (p q : T ⟶ X.left) (hpq : p ≫ f.left = q ≫ f.left) :
      p.appTop r = q.appTop r := by
    let T' : Over S := Over.mk (p ≫ X.hom)
    let p' : T' ⟶ X := Over.homMk p rfl
    have hq : q ≫ X.hom = p ≫ X.hom := by
      rw [← f.w, ← Category.assoc, ← Category.assoc, hpq]
    let q' : T' ⟶ X := Over.homMk q hq
    have hpq' : p' ≫ f = q' ≫ f := Over.OverMorphism.ext hpq
    apply PullHomScalars.Construction.line_comparison_scalar_invariant f L M b a p' q' hpq'
    exact ha T' p' q' hpq'
  obtain ⟨s, hs⟩ := FunctionDescent.Construction.globalSection_desc f.left r hr
  have hunitr : IsUnit r :=
    ((isUnit_iff_isIso c).mpr hc).map (LineEndRigidity.Construction.lineBundleEndRingEquiv (L.pullback f.left)).toMonoidHom
  have hunits : IsUnit s := FramedLineIso.Construction.isUnit_of_surjective_pullback f.left s (hs.symm ▸ hunitr)
  let d₀ : End L.sheaf := Quotients.FiniteDescent.ModuleScalarsApp.Construction.ModuleScalars.scalar L.sheaf s
  have : IsIso d₀ := (isUnit_iff_isIso d₀).mp (hunits.map (Quotients.FiniteDescent.ModuleScalarsApp.Construction.ModuleScalars.scalarHom _))
  let d : L.sheaf ≅ M.sheaf := asIso d₀ ≪≫ b
  refine ⟨d, ?_⟩
  change (Scheme.Modules.pullback f.left).map (d₀ ≫ b.hom) = a.hom
  rw [Functor.map_comp]
  change (Scheme.Modules.pullback f.left).map (Quotients.FiniteDescent.ModuleScalarsApp.Construction.ModuleScalars.scalar L.sheaf s) ≫ _ = _
  rw [Quotients.FiniteDescent.ModuleScalarsApp.Construction.ModuleScalars.pullback_scalar, hs]
  erw [LineEndRigidity.Construction.scalar_lineBundleEndRingEquiv (L.pullback f.left) c]
  change (a.hom ≫ (Scheme.Modules.pullback f.left).map b.inv) ≫
      (Scheme.Modules.pullback f.left).map b.hom = a.hom
  erw [Category.assoc, ← Functor.map_comp, Iso.inv_hom_id,
    (Scheme.Modules.pullback f.left).map_id M.sheaf, Category.comp_id]

end Construction

end

end OAI.AlgebraicGeometry.AbelianScheme.CentralAction.LocallyComparedDescent
