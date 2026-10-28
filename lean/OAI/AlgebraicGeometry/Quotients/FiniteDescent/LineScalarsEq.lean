import OAI.AlgebraicGeometry.Quotients.FiniteDescent.ModuleScalarsApp
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.LineEndomorphismsComm
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.PullbackScalarsValue

/-! # Line Scalars Eq -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.LineScalarsEq.Construction.LineScalars

noncomputable section

/-! Frame coordinates for line-bundle endomorphisms and faithful scalar action. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X Y : Scheme.{u}}

def frameValue {M : X.Modules} (e : M ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X) (a : End M) : Γ(X, ⊤) :=
  AbelianModuli.HilbertConstruction.Frame.Coordinates.structureModuleEndValue X (e.inv ≫ a ≫ e.hom)

theorem frameValue_independent {M : X.Modules} (e f : M ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X) (a : End M) :
    frameValue e a = frameValue f a :=
  congrArg (AbelianModuli.HilbertConstruction.Frame.Coordinates.structureModuleEndValue X) (LineEndomorphismsComm.Construction.LineEndomorphisms.frame_independent e f a)

theorem frameValue_pullback (f : X ⟶ Y) {M : Y.Modules}
    (e : M ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y)
    (e' : (Scheme.Modules.pullback f).obj M ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X) (a : End M) :
    frameValue e' ((Scheme.Modules.pullback f).map a) = f.appTop (frameValue e a) := by
  let ec := (Scheme.Modules.pullback f).mapIso e ≪≫ AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso f
  rw [frameValue_independent e' ec]
  have hc : ec.inv ≫ (Scheme.Modules.pullback f).map a ≫ ec.hom =
      (AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso f).inv ≫
        (Scheme.Modules.pullback f).map (e.inv ≫ a ≫ e.hom) ≫
          (AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso f).hom := by
    simp only [ec, Iso.trans_inv, Iso.trans_hom, Functor.mapIso_inv, Functor.mapIso_hom,
      Functor.map_comp, Category.assoc]
  exact (congrArg (AbelianModuli.HilbertConstruction.Frame.Coordinates.structureModuleEndValue X) hc).trans (PullbackScalarsValue.Construction.PullbackScalars.value_pullback f _)

theorem frameValue_functorComparison {F G : Y.Modules ⥤ X.Modules} (δ : F ≅ G)
    {M : Y.Modules} (e : F.obj M ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X)
    (e' : G.obj M ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X) (a : End M) :
    frameValue e (F.map a) = frameValue e' (G.map a) := by
  let ec := δ.app M ≪≫ e'
  rw [frameValue_independent e ec]
  have hn : F.map a ≫ (δ.app M).hom = (δ.app M).hom ≫ G.map a := δ.hom.naturality a
  have hc : ec.inv ≫ F.map a ≫ ec.hom = e'.inv ≫ G.map a ≫ e'.hom := by
    simp only [ec, Iso.trans_inv, Iso.trans_hom, Category.assoc]
    rw [← Category.assoc (F.map a) (δ.app M).hom e'.hom, hn, Category.assoc,
      Iso.inv_hom_id_assoc]
  exact congrArg (AbelianModuli.HilbertConstruction.Frame.Coordinates.structureModuleEndValue X) hc

theorem scalar_eq_of_frame {M : X.Modules} (e : M ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X) (a : End M) :
    ModuleScalarsApp.Construction.ModuleScalars.scalar M (frameValue e a) = a := by
  have h : ModuleScalarsApp.Construction.ModuleScalars.scalar (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X) (frameValue e a) = e.inv ≫ a ≫ e.hom := by
    apply AbelianModuli.HilbertConstruction.Global.Sections.structureModuleEndValue_injective X
    exact ModuleScalarsApp.Construction.ModuleScalars.structure_value _
  apply (cancel_epi e.inv).mp
  apply (cancel_mono e.hom).mp
  simpa only [Category.assoc, ModuleScalarsApp.Construction.ModuleScalars.scalar_naturality e.hom,
    Iso.inv_hom_id_assoc] using h

theorem scalar_injective (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X) : Function.Injective (ModuleScalarsApp.Construction.ModuleScalars.scalarHom L.sheaf) := by
  intro r s h
  apply TopCat.Presheaf.section_ext X.sheaf ⊤ r s
  intro x _
  obtain ⟨U, hx, ⟨e⟩⟩ := L.locallyTrivial x
  have hl : U.ι.appTop r = U.ι.appTop s := by
    have he := congrArg (fun a : End L.sheaf => (Scheme.Modules.pullback U.ι).map a) h
    change (Scheme.Modules.pullback U.ι).map (ModuleScalarsApp.Construction.ModuleScalars.scalar L.sheaf r) =
      (Scheme.Modules.pullback U.ι).map (ModuleScalarsApp.Construction.ModuleScalars.scalar L.sheaf s) at he
    rw [ModuleScalarsApp.Construction.ModuleScalars.pullback_scalar, ModuleScalarsApp.Construction.ModuleScalars.pullback_scalar] at he
    have hO : ModuleScalarsApp.Construction.ModuleScalars.scalar (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule U.toScheme) (U.ι.appTop r) =
        ModuleScalarsApp.Construction.ModuleScalars.scalar (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule U.toScheme) (U.ι.appTop s) := by
      apply (cancel_epi e.hom).mp
      exact (ModuleScalarsApp.Construction.ModuleScalars.scalar_naturality e.hom _).symm.trans
        ((congrArg (fun a => a ≫ e.hom) he).trans (ModuleScalarsApp.Construction.ModuleScalars.scalar_naturality e.hom _))
    have hv := congrArg (AbelianModuli.HilbertConstruction.Frame.Coordinates.structureModuleEndValue U.toScheme) hO
    simpa only [ModuleScalarsApp.Construction.ModuleScalars.structure_value] using hv
  let y : U.toScheme := ⟨x, hx⟩
  apply (ConcreteCategory.bijective_of_isIso (U.ι.stalkMap y)).1
  change U.ι.stalkMap y (X.presheaf.germ ⊤ (U.ι y) trivial r) =
    U.ι.stalkMap y (X.presheaf.germ ⊤ (U.ι y) trivial s)
  exact (U.ι.germ_stalkMap_apply ⊤ y (by trivial) r).trans
    ((congrArg (U.toScheme.presheaf.germ ⊤ y (by trivial)) hl).trans
      (U.ι.germ_stalkMap_apply ⊤ y (by trivial) s).symm)

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.LineScalarsEq.Construction.LineScalars
