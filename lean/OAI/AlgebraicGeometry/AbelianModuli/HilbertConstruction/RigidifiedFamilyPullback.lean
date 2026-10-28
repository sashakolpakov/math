import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.RigidifiedLineCanonicalComparisons

/-! # Rigidified Family Pullback -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Native products of a fixed family give a coherent pullback operation
on actual zero-rigidified line objects, including heterogeneous lines. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
universe u
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PoincareNormalization

section
variable {S : Scheme.{u}} {g : ℕ} (A : Abelian.Schemes.AbelianScheme g S)
  {T U V : Over S}

def RigidifiedLineBundles.RigidifiedLineBundle.familyPullback (L : RigidifiedLineBundles.RigidifiedLineBundle (Isogenies.NeighborCounting.PoincareNormalization.familyZero A T).left) (f : U ⟶ T) :
    RigidifiedLineBundles.RigidifiedLineBundle (Isogenies.NeighborCounting.PoincareNormalization.familyZero A U).left :=
  L.pullbackSquare (f ▷ A.scheme).left (Isogenies.NeighborCounting.PoincareNormalization.familyZero A U).left f.left
    (congrArg Over.Hom.left (Isogenies.NeighborCounting.PoincareNormalization.familyZero_naturality A f))

def RigidifiedLineBundles.RigidifiedLineBundle.familyPullbackCompIso (L : RigidifiedLineBundles.RigidifiedLineBundle (Isogenies.NeighborCounting.PoincareNormalization.familyZero A T).left)
    (f : U ⟶ T) (h : V ⟶ U) :
    RigidifiedLineBundles.RigidifiedLineBundleIso ((L.familyPullback A f).familyPullback A h)
      (L.familyPullback A (h ≫ f)) := by
  have hf : (Isogenies.NeighborCounting.PoincareNormalization.familyZero A U).left ≫ (f ▷ A.scheme).left =
      f.left ≫ (Isogenies.NeighborCounting.PoincareNormalization.familyZero A T).left :=
    congrArg Over.Hom.left (Isogenies.NeighborCounting.PoincareNormalization.familyZero_naturality A f)
  have hh : (Isogenies.NeighborCounting.PoincareNormalization.familyZero A V).left ≫ (h ▷ A.scheme).left =
      h.left ≫ (Isogenies.NeighborCounting.PoincareNormalization.familyZero A U).left :=
    congrArg Over.Hom.left (Isogenies.NeighborCounting.PoincareNormalization.familyZero_naturality A h)
  have hc : (Isogenies.NeighborCounting.PoincareNormalization.familyZero A V).left ≫ ((h ▷ A.scheme).left ≫ (f ▷ A.scheme).left) =
      (h.left ≫ f.left) ≫ (Isogenies.NeighborCounting.PoincareNormalization.familyZero A T).left := by
    rw [← Category.assoc, hh, Category.assoc, hf, ← Category.assoc]
  have hm : (h ▷ A.scheme).left ≫ (f ▷ A.scheme).left = ((h ≫ f) ▷ A.scheme).left :=
    congrArg Over.Hom.left (comp_whiskerRight h f A.scheme).symm
  exact (L.pullbackSquareCompIso (f ▷ A.scheme).left (Isogenies.NeighborCounting.PoincareNormalization.familyZero A U).left f.left hf
      (h ▷ A.scheme).left (Isogenies.NeighborCounting.PoincareNormalization.familyZero A V).left h.left hh hc).trans
    (L.pullbackSquareCongrIso ((h ▷ A.scheme).left ≫ (f ▷ A.scheme).left)
      ((h ≫ f) ▷ A.scheme).left (Isogenies.NeighborCounting.PoincareNormalization.familyZero A V).left (h.left ≫ f.left) (h ≫ f).left
      hc (congrArg Over.Hom.left (Isogenies.NeighborCounting.PoincareNormalization.familyZero_naturality A (h ≫ f))) hm rfl)

def RigidifiedLineBundles.RigidifiedLineBundle.familyPullbackCongrIso (L : RigidifiedLineBundles.RigidifiedLineBundle (Isogenies.NeighborCounting.PoincareNormalization.familyZero A T).left)
    (f f' : U ⟶ T) (h : f = f') :
    RigidifiedLineBundles.RigidifiedLineBundleIso (L.familyPullback A f) (L.familyPullback A f') := by
  subst f'
  exact RigidifiedLineBundles.RigidifiedLineBundleIso.refl _

end

variable {S : Scheme.{u}} {g : ℕ} (A : Abelian.Schemes.AbelianScheme g S)
  {T U V W : Over S}

def RigidifiedLineBundles.RigidifiedLineBundleIso.familyPullback {L M : RigidifiedLineBundles.RigidifiedLineBundle (Isogenies.NeighborCounting.PoincareNormalization.familyZero A T).left}
    (e : RigidifiedLineBundles.RigidifiedLineBundleIso L M) (f : U ⟶ T) :
    RigidifiedLineBundles.RigidifiedLineBundleIso (L.familyPullback A f) (M.familyPullback A f) :=
  e.pullbackSquare (f ▷ A.scheme).left (Isogenies.NeighborCounting.PoincareNormalization.familyZero A U).left f.left
    (congrArg Over.Hom.left (Isogenies.NeighborCounting.PoincareNormalization.familyZero_naturality A f))

/-- Restriction of a comparison between lines from different parameter
schemes, with the canonical composition maps retained. -/
def RigidifiedLineBundles.RigidifiedLineBundleIso.familyPullbackTo
    {L : RigidifiedLineBundles.RigidifiedLineBundle (Isogenies.NeighborCounting.PoincareNormalization.familyZero A V).left}
    {M : RigidifiedLineBundles.RigidifiedLineBundle (Isogenies.NeighborCounting.PoincareNormalization.familyZero A W).left}
    (a : T ⟶ V) (b : T ⟶ W)
    (e : RigidifiedLineBundles.RigidifiedLineBundleIso (L.familyPullback A a) (M.familyPullback A b))
    (t : U ⟶ T) (a' : U ⟶ V) (b' : U ⟶ W)
    (ha : t ≫ a = a') (hb : t ≫ b = b') :
    RigidifiedLineBundles.RigidifiedLineBundleIso (L.familyPullback A a') (M.familyPullback A b') :=
  ((L.familyPullbackCongrIso A _ _ ha).symm.trans (L.familyPullbackCompIso A a t).symm).trans
    ((e.familyPullback A t).trans
      ((M.familyPullbackCompIso A b t).trans (M.familyPullbackCongrIso A _ _ hb)))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
