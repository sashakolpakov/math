import OAI.AlgebraicGeometry.AbelianScheme.CentralAction.LineEndScalars
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.ModuleScalarsApp
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.ProperFunctionsEq

/-! # Line End Rigidity -/

namespace OAI.AlgebraicGeometry.AbelianScheme.CentralAction.LineEndRigidity

noncomputable section

/-! Intrinsic endomorphism scalars and their pullback give rigidity of
line-bundle isomorphisms on connected reduced proper schemes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

set_option backward.isDefEq.respectTransparency.types false

namespace Construction

universe u
variable {X Y : Scheme.{u}}

theorem lineBundle_scalar_injective (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X) :
    Function.Injective (Quotients.FiniteDescent.ModuleScalarsApp.Construction.ModuleScalars.scalarHom L.sheaf) := by
  intro r s hrs
  let U : X → X.Opens := fun x => (L.locallyTrivial x).choose
  let e (x : X) := L.overFrameIso (U x) (L.locallyTrivial x).choose_spec.2.some
  let F : TopCat.Sheaf AddCommGrpCat X :=
    ⟨(AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X).presheaf, (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X).isSheaf⟩
  apply F.eq_of_locally_eq' U ⊤ (fun x => (U x).leTop)
  · intro x _
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨x, (L.locallyTrivial x).choose_spec.1⟩
  · intro x
    apply LineEndScalars.Construction.scalar_eq_of_linearFrame (R := Γ(X, U x)) (LineEndScalars.Construction.lineFrameAt L (e x) le_rfl)
    intro z
    exact congrArg (fun a : End L.sheaf => a.app (U x) z) hrs

theorem lineBundle_scalar_surjective (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X) :
    Function.Surjective (Quotients.FiniteDescent.ModuleScalarsApp.Construction.ModuleScalars.scalarHom L.sheaf) := by
  intro a
  obtain ⟨r, hr⟩ := LineEndScalars.Construction.lineEnd_exists_global_scalar L a
  refine ⟨r, ?_⟩
  apply Scheme.Modules.hom_ext
  intro U
  ext z
  exact (hr U z).symm

/-- The endomorphism ring of an actual line bundle is canonically the
ring of global functions. -/
def lineBundleEndRingEquiv (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X) : End L.sheaf ≃+* Γ(X, ⊤) :=
  (RingEquiv.ofBijective (Quotients.FiniteDescent.ModuleScalarsApp.Construction.ModuleScalars.scalarHom L.sheaf)
    ⟨lineBundle_scalar_injective L, lineBundle_scalar_surjective L⟩).symm

theorem lineBundleEndRingEquiv_scalar (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X) (r : Γ(X, ⊤)) :
    lineBundleEndRingEquiv L (Quotients.FiniteDescent.ModuleScalarsApp.Construction.ModuleScalars.scalar L.sheaf r) = r :=
  (lineBundleEndRingEquiv L).apply_symm_apply r

theorem scalar_lineBundleEndRingEquiv (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X) (a : End L.sheaf) :
    Quotients.FiniteDescent.ModuleScalarsApp.Construction.ModuleScalars.scalar L.sheaf (lineBundleEndRingEquiv L a) = a :=
  (lineBundleEndRingEquiv L).symm_apply_apply a

/-- The intrinsic endomorphism scalar commutes with arbitrary pullback. -/
theorem lineBundleEndRingEquiv_pullback (f : X ⟶ Y) (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle Y)
    (a : End L.sheaf) :
    lineBundleEndRingEquiv (L.pullback f) ((Scheme.Modules.pullback f).map a) =
      f.appTop (lineBundleEndRingEquiv L a) := by
  conv_lhs => rw [← scalar_lineBundleEndRingEquiv L a]
  rw [Quotients.FiniteDescent.ModuleScalarsApp.Construction.ModuleScalars.pullback_scalar]
  exact lineBundleEndRingEquiv_scalar (L.pullback f) _

theorem lineBundle_end_pullback_injective (f : X ⟶ Y)
    (hf : Function.Injective f.appTop) (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle Y) :
    Function.Injective (fun a : End L.sheaf => (Scheme.Modules.pullback f).map a) := by
  intro a b hab
  apply (lineBundleEndRingEquiv L).injective
  apply hf
  rw [← lineBundleEndRingEquiv_pullback, ← lineBundleEndRingEquiv_pullback]
  exact congrArg (lineBundleEndRingEquiv (L.pullback f)) hab

theorem lineBundle_end_pullback_bijective (f : X ⟶ Y)
    (hf : Function.Bijective f.appTop) (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle Y) :
    Function.Bijective (fun a : End L.sheaf => (Scheme.Modules.pullback f).map a) := by
  refine ⟨lineBundle_end_pullback_injective f hf.1 L, ?_⟩
  intro b
  obtain ⟨r, hr⟩ := hf.2 (lineBundleEndRingEquiv (L.pullback f) b)
  refine ⟨Quotients.FiniteDescent.ModuleScalarsApp.Construction.ModuleScalars.scalar L.sheaf r, ?_⟩
  change (Scheme.Modules.pullback f).map (Quotients.FiniteDescent.ModuleScalarsApp.Construction.ModuleScalars.scalar L.sheaf r) = b
  rw [Quotients.FiniteDescent.ModuleScalarsApp.Construction.ModuleScalars.pullback_scalar, hr]
  exact scalar_lineBundleEndRingEquiv (L.pullback f) b

/-- Once one comparison is an isomorphism, injectivity on global
functions detects equality of both line-bundle morphisms after pullback. -/
theorem lineBundle_hom_ext_of_pullback (f : X ⟶ Y)
    (hf : Function.Injective f.appTop) (L M : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle Y)
    (a b : L.sheaf ⟶ M.sheaf) [IsIso a]
    (h : (Scheme.Modules.pullback f).map a = (Scheme.Modules.pullback f).map b) : a = b := by
  apply (cancel_epi (inv a)).mp
  apply lineBundle_end_pullback_injective f hf M
  simp only [Functor.map_comp, h]

/-- Any map from a nonempty scheme detects line-bundle endomorphisms on
a connected reduced proper scheme over a field. -/
theorem proper_lineBundle_end_pullback_injective
    {k : Type u} [Field k] (Y : Over (Spec (.of k)))
    [IsProper Y.hom] [ConnectedSpace Y.left] [IsReduced Y.left]
    (f : X ⟶ Y.left) [Nonempty X] (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle Y.left) :
    Function.Injective (fun a : End L.sheaf => (Scheme.Modules.pullback f).map a) := by
  let := (Quotients.FiniteDescent.ProperFunctionsEq.Construction.ProperFunctions.globalSections_isField Y).toField
  have : Nontrivial Γ(X, ⊤) :=
    (X.presheaf.germ ⊤ (Nonempty.some ‹Nonempty X›) trivial).hom.domain_nontrivial
  exact lineBundle_end_pullback_injective f f.appTop.hom.injective L

theorem proper_lineBundle_iso_hom_ext
    {k : Type u} [Field k] (Y : Over (Spec (.of k)))
    [IsProper Y.hom] [ConnectedSpace Y.left] [IsReduced Y.left]
    (f : X ⟶ Y.left) [Nonempty X] (L M : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle Y.left)
    (a b : L.sheaf ≅ M.sheaf)
    (h : (Scheme.Modules.pullback f).map a.hom = (Scheme.Modules.pullback f).map b.hom) :
    a.hom = b.hom := by
  apply (cancel_epi a.inv).mp
  apply proper_lineBundle_end_pullback_injective Y f M
  simp only [Functor.map_comp, h]

/-- Between pointed connected reduced proper schemes, restriction is a
bijection on global functions. The base-field identifications are proved
using the actual point and structure maps. -/
theorem proper_pointed_appTop_bijective
    {k : Type u} [Field k] (X Y : Over (Spec (.of k)))
    [IsProper X.hom] [ConnectedSpace X.left] [IsReduced X.left]
    [IsProper Y.hom] [ConnectedSpace Y.left] [IsReduced Y.left]
    (f : X ⟶ Y) (z : Spec (.of k) ⟶ X.left) (hz : z ≫ X.hom = 𝟙 _) :
    Function.Bijective f.left.appTop := by
  have : IsIso X.hom.appTop := Quotients.FiniteDescent.ProperFunctionsEq.Construction.ProperFunctions.isIso_appTop_of_section X z hz
  have : IsIso Y.hom.appTop := Quotients.FiniteDescent.ProperFunctionsEq.Construction.ProperFunctions.isIso_appTop_of_section Y (z ≫ f.left) (by
    rw [Category.assoc, f.w, hz])
  have hc : IsIso (Y.hom.appTop ≫ f.left.appTop) := by
    rw [← Scheme.Hom.comp_appTop, f.w]
    infer_instance
  have : IsIso f.left.appTop := (isIso_comp_left_iff Y.hom.appTop f.left.appTop).mp hc
  exact ConcreteCategory.bijective_of_isIso f.left.appTop

end Construction

end

end OAI.AlgebraicGeometry.AbelianScheme.CentralAction.LineEndRigidity
