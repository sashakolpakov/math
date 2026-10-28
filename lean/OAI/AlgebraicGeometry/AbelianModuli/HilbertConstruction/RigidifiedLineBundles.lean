import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles

/-! # Rigidified Line Bundles -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.RigidifiedLineBundles

noncomputable section

/-! Actual line bundles with a chosen trivialization along a section, and isomorphisms preserving it. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X S : Scheme.{u}}

structure RigidifiedLineBundle (x : S ⟶ X) where
  lineBundle : Line.Bundles.LineBundle X
  rigidification : (Scheme.Modules.pullback x).obj lineBundle.sheaf ≅ Line.Bundles.structureModule S

structure RigidifiedLineBundleIso {x : S ⟶ X} (L M : RigidifiedLineBundle x) where
  underlying : L.lineBundle.sheaf ≅ M.lineBundle.sheaf
  normalized : (Scheme.Modules.pullback x).map underlying.hom ≫ M.rigidification.hom =
    L.rigidification.hom

namespace RigidifiedLineBundleIso

variable {x : S ⟶ X} {L M N : RigidifiedLineBundle x}

@[ext]
theorem ext {e f : RigidifiedLineBundleIso L M} (h : e.underlying = f.underlying) : e = f := by
  cases e
  cases f
  cases h
  rfl

def refl (L : RigidifiedLineBundle x) : RigidifiedLineBundleIso L L where
  underlying := Iso.refl _
  normalized := by
    change (Scheme.Modules.pullback x).map (𝟙 L.lineBundle.sheaf) ≫ L.rigidification.hom = _
    rw [(Scheme.Modules.pullback x).map_id, Category.id_comp]

def trans (e : RigidifiedLineBundleIso L M) (f : RigidifiedLineBundleIso M N) :
    RigidifiedLineBundleIso L N where
  underlying := e.underlying ≪≫ f.underlying
  normalized := by
    rw [Iso.trans_hom, Functor.map_comp, Category.assoc, f.normalized, e.normalized]

def symm (e : RigidifiedLineBundleIso L M) : RigidifiedLineBundleIso M L where
  underlying := e.underlying.symm
  normalized := by
    apply (cancel_epi ((Scheme.Modules.pullback x).map e.underlying.hom)).mp
    rw [← e.normalized, Iso.symm_hom, ← Category.assoc, ← Functor.map_comp,
      e.underlying.hom_inv_id, (Scheme.Modules.pullback x).map_id, Category.id_comp]

end RigidifiedLineBundleIso

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.RigidifiedLineBundles
