import OAI.AlgebraicGeometry.AbelianScheme.CentralAction.FunctionDescent
import OAI.AlgebraicGeometry.AbelianScheme.CentralAction.LineEndRigidity
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.PullbackScalarsValue

/-! # Framed Line Iso -/

namespace OAI.AlgebraicGeometry.AbelianScheme.CentralAction.FramedLineIso

noncomputable section

/-! Scalar coordinates of framed line-bundle isomorphisms commute with
arbitrary pullback. Surjectivity reflects invertible regular functions. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

set_option backward.isDefEq.respectTransparency.types false

namespace Construction

universe u
variable {X Y : Scheme.{u}}

def pulledLineFrame (f : X ⟶ Y) (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle Y)
    (e : L.sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y) :
    (L.pullback f).sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X :=
  (Scheme.Modules.pullback f).mapIso e ≪≫ AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso f

def framedLineIsoScalar (L M : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X)
    (l : L.sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X) (m : M.sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X)
    (a : L.sheaf ≅ M.sheaf) : Γ(X, ⊤) :=
  AbelianModuli.HilbertConstruction.Frame.Coordinates.structureModuleEndValue X (l.inv ≫ a.hom ≫ m.hom)

theorem framedLineIsoScalar_isUnit (L M : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X)
    (l : L.sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X) (m : M.sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X)
    (a : L.sheaf ≅ M.sheaf) : IsUnit (framedLineIsoScalar L M l m a) :=
  ((isUnit_iff_isIso (l.inv ≫ a.hom ≫ m.hom)).mpr inferInstance).map
    (AbelianModuli.HilbertConstruction.Frame.Coordinates.structureModuleEndValue X)

theorem framedLineIsoScalar_pullback (f : X ⟶ Y) (L M : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle Y)
    (l : L.sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y) (m : M.sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y)
    (a : L.sheaf ≅ M.sheaf) :
    framedLineIsoScalar (L.pullback f) (M.pullback f)
      (pulledLineFrame f L l) (pulledLineFrame f M m)
      ((Scheme.Modules.pullback f).mapIso a) =
        f.appTop (framedLineIsoScalar L M l m a) := by
  change AbelianModuli.HilbertConstruction.Frame.Coordinates.structureModuleEndValue X
    (((AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso f).inv ≫ (Scheme.Modules.pullback f).map l.inv) ≫
      (Scheme.Modules.pullback f).map a.hom ≫
        (Scheme.Modules.pullback f).map m.hom ≫ (AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso f).hom) = _
  simp only [Category.assoc, ← Functor.map_comp_assoc]
  exact Quotients.FiniteDescent.PullbackScalarsValue.Construction.PullbackScalars.value_pullback f (l.inv ≫ a.hom ≫ m.hom)

theorem isUnit_of_surjective_pullback (f : X ⟶ Y) [Surjective f]
    (r : Γ(Y, ⊤)) (hr : IsUnit (f.appTop r)) : IsUnit r := by
  apply (AbelianModuli.HilbertConstruction.Scalar.Nonvanishing.global_isUnit_iff_basicOpen_eq_top r).mpr
  apply top_unique
  intro y _
  obtain ⟨x, rfl⟩ := f.surjective y
  have hpre : f ⁻¹ᵁ Y.basicOpen r = ⊤ :=
    (f.preimage_basicOpen_top r).trans (X.basicOpen_of_isUnit hr)
  exact (show x ∈ f ⁻¹ᵁ Y.basicOpen r from hpre.symm ▸ trivial)

end Construction

end

end OAI.AlgebraicGeometry.AbelianScheme.CentralAction.FramedLineIso
