import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.RigidifiedLineBundles
import OAI.AlgebraicGeometry.FormalGeometry.Completion.Rigidified.IsoPullback

/-! # Rigidified Line Square Pullback -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Actual pullback of rigidified line objects and their isomorphisms
along a commuting square. The canonical composition comparison preserves
the specified rigidification; this supplies the coherence needed in
Zariski object descent. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u
open OAI.AlgebraicGeometry.FormalGeometry.Completion.Rigidified.IsoPullback.Construction

section
variable {X Y Z S T U : Scheme.{u}} {x : S ⟶ X}

def RigidifiedLineBundles.RigidifiedLineBundle.pullbackSquare (L : RigidifiedLineBundles.RigidifiedLineBundle x) (f : Y ⟶ X) (y : T ⟶ Y) (a : T ⟶ S)
    (h : y ≫ f = a ≫ x) : RigidifiedLineBundles.RigidifiedLineBundle y where
  lineBundle := L.lineBundle.pullback f
  rigidification := FormalGeometry.Completion.Rigidified.FrameScalar.Construction.rigidificationBaseChangeIso f y a x h L.lineBundle.sheaf L.rigidification

/-- Iterating square pullback agrees with composition on the actual
line object and its chosen zero trivialization. -/
def RigidifiedLineBundles.RigidifiedLineBundle.pullbackSquareCompIso (L : RigidifiedLineBundles.RigidifiedLineBundle x)
    (f : Y ⟶ X) (y : T ⟶ Y) (a : T ⟶ S) (h : y ≫ f = a ≫ x)
    (k : Z ⟶ Y) (z : U ⟶ Z) (b : U ⟶ T) (hk : z ≫ k = b ≫ y)
    (hc : z ≫ (k ≫ f) = (b ≫ a) ≫ x) :
    RigidifiedLineBundles.RigidifiedLineBundleIso ((L.pullbackSquare f y a h).pullbackSquare k z b hk)
      (L.pullbackSquare (k ≫ f) z (b ≫ a) hc) where
  underlying := (Scheme.Modules.pullbackComp k f).app L.lineBundle.sheaf
  normalized := by
    change (Scheme.Modules.pullback z).map ((Scheme.Modules.pullbackComp k f).hom.app L.lineBundle.sheaf) ≫
      (FormalGeometry.Completion.Rigidified.FrameScalar.Construction.rigidificationBaseChangeIso (k ≫ f) z (b ≫ a) x hc L.lineBundle.sheaf L.rigidification).hom =
        (FormalGeometry.Completion.Rigidified.FrameScalar.Construction.rigidificationBaseChangeIso k z b y hk
          ((Scheme.Modules.pullback f).obj L.lineBundle.sheaf)
          (FormalGeometry.Completion.Rigidified.FrameScalar.Construction.rigidificationBaseChangeIso f y a x h L.lineBundle.sheaf L.rigidification)).hom
    exact (FormalGeometry.Completion.RigidificationComparisonPasting.Construction.rigidificationBaseChangeIso_paste f k x y a z b hk h hc
      L.lineBundle.sheaf L.rigidification).trans
        (FormalGeometry.Completion.RigidificationComparisonPasting.Construction.rigidificationBaseChangeIso_hom k z b y hk _ _).symm

def RigidifiedLineBundles.RigidifiedLineBundle.pullbackSquareCongrIso (L : RigidifiedLineBundles.RigidifiedLineBundle x)
    (f f' : Y ⟶ X) (y : T ⟶ Y) (a a' : T ⟶ S)
    (h : y ≫ f = a ≫ x) (h' : y ≫ f' = a' ≫ x)
    (hf : f = f') (ha : a = a') :
    RigidifiedLineBundles.RigidifiedLineBundleIso (L.pullbackSquare f y a h) (L.pullbackSquare f' y a' h') := by
  subst f'
  subst a'
  exact RigidifiedLineBundles.RigidifiedLineBundleIso.refl _

end

variable {X Y S T : Scheme.{u}} {x : S ⟶ X} {L M : RigidifiedLineBundles.RigidifiedLineBundle x}

def RigidifiedLineBundles.RigidifiedLineBundleIso.pullbackSquare (e : RigidifiedLineBundles.RigidifiedLineBundleIso L M)
    (f : Y ⟶ X) (y : T ⟶ Y) (a : T ⟶ S) (h : y ≫ f = a ≫ x) :
    RigidifiedLineBundles.RigidifiedLineBundleIso (L.pullbackSquare f y a h) (M.pullbackSquare f y a h) where
  underlying := (Scheme.Modules.pullback f).mapIso e.underlying
  normalized := by
    let α := Scheme.Modules.pullbackComp y f ≪≫ Scheme.Modules.pullbackCongr h ≪≫
      (Scheme.Modules.pullbackComp a x).symm
    change (Scheme.Modules.pullback y).map ((Scheme.Modules.pullback f).map e.underlying.hom) ≫
      (FormalGeometry.Completion.Rigidified.FrameScalar.Construction.rigidificationBaseChangeIso f y a x h M.lineBundle.sheaf M.rigidification).hom =
        (FormalGeometry.Completion.Rigidified.FrameScalar.Construction.rigidificationBaseChangeIso f y a x h L.lineBundle.sheaf L.rigidification).hom
    rw [FormalGeometry.Completion.RigidificationComparisonPasting.Construction.rigidificationBaseChangeIso_hom, FormalGeometry.Completion.RigidificationComparisonPasting.Construction.rigidificationBaseChangeIso_hom]
    have hn := α.hom.naturality e.underlying.hom
    change (Scheme.Modules.pullback y).map ((Scheme.Modules.pullback f).map e.underlying.hom) ≫
        α.hom.app M.lineBundle.sheaf =
      α.hom.app L.lineBundle.sheaf ≫
        (Scheme.Modules.pullback a).map ((Scheme.Modules.pullback x).map e.underlying.hom) at hn
    change (Scheme.Modules.pullback y).map ((Scheme.Modules.pullback f).map e.underlying.hom) ≫
      α.hom.app M.lineBundle.sheaf ≫ (Scheme.Modules.pullback a).map M.rigidification.hom ≫
        (Line.Bundles.structureModulePullbackIso a).hom =
      α.hom.app L.lineBundle.sheaf ≫ (Scheme.Modules.pullback a).map L.rigidification.hom ≫
        (Line.Bundles.structureModulePullbackIso a).hom
    rw [← Category.assoc, hn, Category.assoc, ← Functor.map_comp_assoc, e.normalized]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
