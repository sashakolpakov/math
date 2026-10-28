import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.FamilyZeroFrames

/-! # Family Normalized Pullback -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.FamilyNormalizedPullback.Construction

noncomputable section

/-! Pulling back a family comparison preserves its original zero
normalization, including the actual module pullback comparisons. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PoincareNormalization
open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers OAI.AlgebraicGeometry.Picard.PoincareBundle.GlobalPullbackFrame OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.KernelLinearization
open OAI.AlgebraicGeometry.Picard.PoincareBundle.PullbackFiberComposition OAI.AlgebraicGeometry.Picard.PoincareBundle.PullHom Pseudofunctor.LocallyDiscreteOpToCat

variable {S : Scheme.{u}} {d : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme d S) {V T U : Over S}

theorem familyMap_comp (t : U ⟶ T) (a : T ⟶ V) (a' : U ⟶ V) (ha : t ≫ a = a') :
    (t ▷ A.scheme) ≫ (a ▷ A.scheme) = a' ▷ A.scheme :=
  (comp_whiskerRight t a A.scheme).symm.trans (congrArg (fun m => m ▷ A.scheme) ha)

variable (a : T ⟶ V) (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (V ⊗ A.scheme).left)
variable (eL : (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullback (Isogenies.NeighborCounting.PoincareNormalization.familyZero A V).left L).sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule V.left)
variable (b : T ⟶ V)
variable (e : (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullback (a ▷ A.scheme).left L).sheaf ≅
  (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullback (b ▷ A.scheme).left L).sheaf)
variable (t : U ⟶ T) (a' b' : U ⟶ V) (hta : t ≫ a = a') (htb : t ≫ b = b')

def familyIsoPullback :
    (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullback (a' ▷ A.scheme).left L).sheaf ≅
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullback (b' ▷ A.scheme).left L).sheaf :=
  Picard.PoincareBundle.PullbackFiberComposition.pullIso (Picard.PoincareBundle.Geometric.KernelLinearization.overModulePullbacks S) (A := V ⊗ A.scheme) (B := V ⊗ A.scheme)
    (M := L.sheaf) (N := L.sheaf)
    (x := a ▷ A.scheme) (y := b ▷ A.scheme) e (t ▷ A.scheme)
    (a' ▷ A.scheme) (b' ▷ A.scheme) (familyMap_comp A t a a' hta) (familyMap_comp A t b b' htb)

theorem familyIsoPullback_normalized
    (he : (Scheme.Modules.pullback (Isogenies.NeighborCounting.PoincareNormalization.familyZero A T).left).map e.hom ≫
      (Isogenies.NeighborCounting.PoincareNormalization.familyPullbackZeroIso A b L eL).hom = (Isogenies.NeighborCounting.PoincareNormalization.familyPullbackZeroIso A a L eL).hom) :
    (Scheme.Modules.pullback (Isogenies.NeighborCounting.PoincareNormalization.familyZero A U).left).map (familyIsoPullback A a L b e t a' b' hta htb).hom ≫
        (Isogenies.NeighborCounting.PoincareNormalization.familyPullbackZeroIso A b' L eL).hom = (Isogenies.NeighborCounting.PoincareNormalization.familyPullbackZeroIso A a' L eL).hom := by
  apply (FamilyZeroFrames.Construction.familyIso_normalized_iff_fiber A a' L eL b' _).mpr
  have hn := (FamilyZeroFrames.Construction.familyIso_normalized_iff_fiber A a L eL b e).mp he
  have htx : t ≫ (Isogenies.NeighborCounting.PoincareNormalization.familyZero A T ≫ (a ▷ A.scheme)) = Isogenies.NeighborCounting.PoincareNormalization.familyZero A U ≫ (a' ▷ A.scheme) := by
    rw [← Category.assoc, ← Isogenies.NeighborCounting.PoincareNormalization.familyZero_naturality A t, Category.assoc, familyMap_comp A t a a' hta]
  have hty : t ≫ (Isogenies.NeighborCounting.PoincareNormalization.familyZero A T ≫ (b ▷ A.scheme)) = Isogenies.NeighborCounting.PoincareNormalization.familyZero A U ≫ (b' ▷ A.scheme) := by
    rw [← Category.assoc, ← Isogenies.NeighborCounting.PoincareNormalization.familyZero_naturality A t, Category.assoc, familyMap_comp A t b b' htb]
  have hfirst := pullHom_pullHom (F := Picard.PoincareBundle.Geometric.KernelLinearization.overModulePullbacks S)
    (X₁ := V ⊗ A.scheme) (X₂ := V ⊗ A.scheme) (M₁ := L.sheaf) (M₂ := L.sheaf)
    (f₁ := a ▷ A.scheme) (f₂ := b ▷ A.scheme) e.hom (t ▷ A.scheme)
    (a' ▷ A.scheme) (b' ▷ A.scheme) (Isogenies.NeighborCounting.PoincareNormalization.familyZero A U)
    (Isogenies.NeighborCounting.PoincareNormalization.familyZero A U ≫ (a' ▷ A.scheme)) (Isogenies.NeighborCounting.PoincareNormalization.familyZero A U ≫ (b' ▷ A.scheme))
    (familyMap_comp A t a a' hta) (familyMap_comp A t b b' htb) rfl rfl
  have hsecond := pullHom_pullHom (F := Picard.PoincareBundle.Geometric.KernelLinearization.overModulePullbacks S)
    (X₁ := V ⊗ A.scheme) (X₂ := V ⊗ A.scheme) (M₁ := L.sheaf) (M₂ := L.sheaf)
    (f₁ := a ▷ A.scheme) (f₂ := b ▷ A.scheme) e.hom (Isogenies.NeighborCounting.PoincareNormalization.familyZero A T)
    (Isogenies.NeighborCounting.PoincareNormalization.familyZero A T ≫ (a ▷ A.scheme)) (Isogenies.NeighborCounting.PoincareNormalization.familyZero A T ≫ (b ▷ A.scheme)) t
    (Isogenies.NeighborCounting.PoincareNormalization.familyZero A U ≫ (a' ▷ A.scheme)) (Isogenies.NeighborCounting.PoincareNormalization.familyZero A U ≫ (b' ▷ A.scheme)) rfl rfl htx hty
  have hbase := Picard.PoincareBundle.PullHom.pullHom_congr (F := Picard.PoincareBundle.Geometric.KernelLinearization.overModulePullbacks S)
    (A := V ⊗ A.scheme) (B := V ⊗ A.scheme) (L := L.sheaf) (M := L.sheaf)
    (x := a ▷ A.scheme) (y := b ▷ A.scheme) e.hom
    (Isogenies.NeighborCounting.PoincareNormalization.familyZero A U ≫ (t ▷ A.scheme)) (t ≫ Isogenies.NeighborCounting.PoincareNormalization.familyZero A T) (Isogenies.NeighborCounting.PoincareNormalization.familyZero_naturality A t)
    (Isogenies.NeighborCounting.PoincareNormalization.familyZero A U ≫ (a' ▷ A.scheme)) (Isogenies.NeighborCounting.PoincareNormalization.familyZero A U ≫ (b' ▷ A.scheme))
    (by rw [Category.assoc, familyMap_comp A t a a' hta])
    (by rw [Category.assoc, familyMap_comp A t b b' htb])
    ((Category.assoc _ _ _).trans htx) ((Category.assoc _ _ _).trans hty)
  have hframe := GlobalFrameComparison.Construction.globallyFramedFiberIso_pullHom (Isogenies.NeighborCounting.PoincareNormalization.familyZero A V)
    (Picard.PoincareBundle.Line.Comparison.Bundle.fromShared L) eL.symm t a b
    (Isogenies.NeighborCounting.PoincareNormalization.familyZero A T ≫ (a ▷ A.scheme)) (Isogenies.NeighborCounting.PoincareNormalization.familyZero A T ≫ (b ▷ A.scheme))
    (Isogenies.NeighborCounting.PoincareNormalization.familyZero_naturality A a).symm (Isogenies.NeighborCounting.PoincareNormalization.familyZero_naturality A b).symm a' b'
    (Isogenies.NeighborCounting.PoincareNormalization.familyZero A U ≫ (a' ▷ A.scheme)) (Isogenies.NeighborCounting.PoincareNormalization.familyZero A U ≫ (b' ▷ A.scheme))
    (Isogenies.NeighborCounting.PoincareNormalization.familyZero_naturality A a').symm (Isogenies.NeighborCounting.PoincareNormalization.familyZero_naturality A b').symm hta htb htx hty
  exact hfirst.trans (hbase.trans (hsecond.symm.trans
    ((congrArg (fun m => pullHom (F := Picard.PoincareBundle.Geometric.KernelLinearization.overModulePullbacks S)
      (X₁ := V ⊗ A.scheme) (X₂ := V ⊗ A.scheme) (M₁ := L.sheaf) (M₂ := L.sheaf)
      (f₁ := Isogenies.NeighborCounting.PoincareNormalization.familyZero A T ≫ (a ▷ A.scheme)) (f₂ := Isogenies.NeighborCounting.PoincareNormalization.familyZero A T ≫ (b ▷ A.scheme)) m t
      (Isogenies.NeighborCounting.PoincareNormalization.familyZero A U ≫ (a' ▷ A.scheme)) (Isogenies.NeighborCounting.PoincareNormalization.familyZero A U ≫ (b' ▷ A.scheme)) htx hty) hn).trans hframe)))

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.FamilyNormalizedPullback.Construction
