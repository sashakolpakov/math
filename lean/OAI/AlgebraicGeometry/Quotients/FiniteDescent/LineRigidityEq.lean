import OAI.AlgebraicGeometry.Quotients.FiniteDescent.LineEndRing

/-! # Line Rigidity Eq -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.LineRigidityEq.Construction.LineRigidity

noncomputable section

/-! Rigidity of line-bundle isomorphisms on a proper connected reduced scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem pullback_end_injective {K : Type u} [Field K]
    (X : Over (Spec (.of K))) [IsProper X.hom] [ConnectedSpace X.left] [IsReduced X.left]
    {Y : Scheme.{u}} [Nonempty Y] (f : Y ⟶ X.left) (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X.left) :
    Function.Injective (fun a : End L.sheaf => (Scheme.Modules.pullback f).map a) := by
  let := (ProperFunctionsEq.Construction.ProperFunctions.globalSections_isField X).toField
  have : Nontrivial Γ(Y, ⊤) :=
    (Y.presheaf.germ ⊤ (Nonempty.some (inferInstance : Nonempty Y)) (by trivial)).hom.domain_nontrivial
  intro a b h
  obtain ⟨r, rfl⟩ := LineEndRing.Construction.LineScalars.scalar_surjective L a
  obtain ⟨s, rfl⟩ := LineEndRing.Construction.LineScalars.scalar_surjective L b
  change (Scheme.Modules.pullback f).map (ModuleScalarsApp.Construction.ModuleScalars.scalar L.sheaf r) =
    (Scheme.Modules.pullback f).map (ModuleScalarsApp.Construction.ModuleScalars.scalar L.sheaf s) at h
  rw [ModuleScalarsApp.Construction.ModuleScalars.pullback_scalar, ModuleScalarsApp.Construction.ModuleScalars.pullback_scalar] at h
  have hr : f.appTop r = f.appTop s := LineScalarsEq.Construction.LineScalars.scalar_injective (L.pullback f) h
  exact congrArg (ModuleScalarsApp.Construction.ModuleScalars.scalarHom L.sheaf) (f.appTop.hom.injective hr)

/-- Once the two bundles are globally isomorphic, restriction to any
nonempty scheme over the proper source detects equality of their morphisms. -/
theorem pullback_hom_injective {K : Type u} [Field K]
    (X : Over (Spec (.of K))) [IsProper X.hom] [ConnectedSpace X.left] [IsReduced X.left]
    {Y : Scheme.{u}} [Nonempty Y] (f : Y ⟶ X.left) (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X.left)
    {M : X.left.Modules} (e : L.sheaf ≅ M) :
    Function.Injective (fun a : L.sheaf ⟶ M => (Scheme.Modules.pullback f).map a) := by
  intro a b h
  apply (cancel_mono e.inv).mp
  apply pullback_end_injective X f L
  change (Scheme.Modules.pullback f).map a = (Scheme.Modules.pullback f).map b at h
  change (Scheme.Modules.pullback f).map (a ≫ e.inv) =
    (Scheme.Modules.pullback f).map (b ≫ e.inv)
  rw [Functor.map_comp, Functor.map_comp, h]

/-- Two line-bundle isomorphisms which agree after a nonempty pullback are equal. -/
theorem iso_eq_of_pullback_eq {K : Type u} [Field K]
    (X : Over (Spec (.of K))) [IsProper X.hom] [ConnectedSpace X.left] [IsReduced X.left]
    {Y : Scheme.{u}} [Nonempty Y] (f : Y ⟶ X.left) (L M : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X.left)
    (e e' : L.sheaf ≅ M.sheaf)
    (h : (Scheme.Modules.pullback f).mapIso e = (Scheme.Modules.pullback f).mapIso e') : e = e' := by
  apply Iso.ext
  exact pullback_hom_injective X f L e (congrArg Iso.hom h)

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.LineRigidityEq.Construction.LineRigidity
