import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.GlobalFrameComparison
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PoincareNormalization
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Comparison

/-! # Family Zero Frames -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.FamilyZeroFrames.Construction

noncomputable section

/-! The original family zero trivializations agree with the coherent
frames obtained by pulling back their single global trivialization. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PoincareNormalization
open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers OAI.AlgebraicGeometry.Picard.PoincareBundle.GlobalPullbackFrame OAI.AlgebraicGeometry.Picard.PoincareBundle.FrameRatioPullback

theorem modulePullbackCongr_symm {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g) :
    (Scheme.Modules.pullbackCongr h.symm).symm = Scheme.Modules.pullbackCongr h := by
  cases h
  rfl

theorem isoFramePath {C : Type*} [Category* C] {U V W X Y Z : C}
    (c : U ≅ V) (h : V ≅ W) (d : X ≅ W) (e : X ≅ Y) (u : Y ≅ Z)
    (h' : W ≅ V) (hh : h'.symm = h) :
    c ≪≫ h ≪≫ d.symm ≪≫ e ≪≫ u =
      c ≪≫ ((u.symm ≪≫ e.symm) ≪≫ (d ≪≫ h')).symm := by
  subst h
  apply Iso.ext
  simp only [Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv, Category.assoc]

variable {S : Scheme.{u}} {d : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme d S) {V T : Over S}
variable (a : T ⟶ V) (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (V ⊗ A.scheme).left)
variable (eL : (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullback (Isogenies.NeighborCounting.PoincareNormalization.familyZero A V).left L).sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule V.left)

def familyZeroFiberFrame :
    AbelianModuli.HilbertConstruction.Line.Bundles.structureModule T.left ≅ Picard.PoincareBundle.Line.Fibers.fiber (Picard.PoincareBundle.Line.Comparison.Bundle.fromShared L)
      (Isogenies.NeighborCounting.PoincareNormalization.familyZero A T ≫ (a ▷ A.scheme)) :=
  Picard.PoincareBundle.GlobalPullbackFrame.atPoint (Isogenies.NeighborCounting.PoincareNormalization.familyZero A V) (Picard.PoincareBundle.Line.Comparison.Bundle.fromShared L) eL.symm a
    (Isogenies.NeighborCounting.PoincareNormalization.familyZero A T ≫ (a ▷ A.scheme)) (Isogenies.NeighborCounting.PoincareNormalization.familyZero_naturality A a).symm

theorem familyPullbackZeroIso_eq_globalFrame :
    Isogenies.NeighborCounting.PoincareNormalization.familyPullbackZeroIso A a L eL =
      (Scheme.Modules.pullbackComp (Isogenies.NeighborCounting.PoincareNormalization.familyZero A T).left (a ▷ A.scheme).left).app L.sheaf ≪≫
        (familyZeroFiberFrame A a L eL).symm := by
  have hc := congrArg (fun e => e.app L.sheaf)
    (modulePullbackCongr_symm (congrArg Over.Hom.left (Isogenies.NeighborCounting.PoincareNormalization.familyZero_naturality A a)))
  unfold familyZeroFiberFrame Picard.PoincareBundle.GlobalPullbackFrame.atPoint
  rw [Picard.PoincareBundle.GlobalPullbackFrame.comparison_eq]
  exact isoFramePath
    ((Scheme.Modules.pullbackComp (Isogenies.NeighborCounting.PoincareNormalization.familyZero A T).left (a ▷ A.scheme).left).app L.sheaf)
    ((Scheme.Modules.pullbackCongr (congrArg Over.Hom.left (Isogenies.NeighborCounting.PoincareNormalization.familyZero_naturality A a))).app L.sheaf)
    ((Scheme.Modules.pullbackComp a.left (Isogenies.NeighborCounting.PoincareNormalization.familyZero A V).left).app L.sheaf)
    ((Scheme.Modules.pullback a.left).mapIso eL) (AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso a.left)
    ((Scheme.Modules.pullbackCongr (congrArg Over.Hom.left (Isogenies.NeighborCounting.PoincareNormalization.familyZero_naturality A a).symm)).app L.sheaf) hc

theorem fiberNormalization_iff {C D : Type*} [Category* C] [Category* D]
    (F : C ⥤ D) {M N : C} {M' N' O : D} (e : M ≅ N)
    (cM : F.obj M ≅ M') (cN : F.obj N ≅ N') (sM : O ≅ M') (sN : O ≅ N') :
    (F.map e.hom ≫ (cN ≪≫ sN.symm).hom = (cM ≪≫ sM.symm).hom) ↔
      (cM.inv ≫ F.map e.hom ≫ cN.hom = (sM.symm ≪≫ sN).hom) := by
  constructor
  · intro h
    apply (cancel_epi cM.hom).mp
    apply (cancel_mono sN.inv).mp
    simpa only [Iso.trans_hom, Iso.symm_hom, Category.assoc,
      Iso.hom_inv_id_assoc, Iso.hom_inv_id, Category.comp_id] using h
  · intro h
    have hh := congrArg (fun m => cM.hom ≫ m ≫ sN.inv) h
    simpa only [Iso.trans_hom, Iso.symm_hom, Category.assoc,
      Iso.hom_inv_id_assoc, Iso.hom_inv_id, Category.comp_id] using hh

theorem familyIso_normalized_iff_fiber (b : T ⟶ V)
    (e : (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullback (a ▷ A.scheme).left L).sheaf ≅
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullback (b ▷ A.scheme).left L).sheaf) :
    ((Scheme.Modules.pullback (Isogenies.NeighborCounting.PoincareNormalization.familyZero A T).left).map e.hom ≫
        (Isogenies.NeighborCounting.PoincareNormalization.familyPullbackZeroIso A b L eL).hom = (Isogenies.NeighborCounting.PoincareNormalization.familyPullbackZeroIso A a L eL).hom) ↔
      (Pseudofunctor.LocallyDiscreteOpToCat.pullHom
          (F := Picard.PoincareBundle.Geometric.KernelLinearization.overModulePullbacks S)
          (X₁ := V ⊗ A.scheme) (X₂ := V ⊗ A.scheme)
          (M₁ := L.sheaf) (M₂ := L.sheaf) (f₁ := a ▷ A.scheme) (f₂ := b ▷ A.scheme)
          e.hom (Isogenies.NeighborCounting.PoincareNormalization.familyZero A T) (Isogenies.NeighborCounting.PoincareNormalization.familyZero A T ≫ (a ▷ A.scheme))
          (Isogenies.NeighborCounting.PoincareNormalization.familyZero A T ≫ (b ▷ A.scheme)) rfl rfl =
        (GlobalFrameComparison.Construction.globallyFramedFiberIso (Isogenies.NeighborCounting.PoincareNormalization.familyZero A V) (Picard.PoincareBundle.Line.Comparison.Bundle.fromShared L) eL.symm
          a b (Isogenies.NeighborCounting.PoincareNormalization.familyZero A T ≫ (a ▷ A.scheme)) (Isogenies.NeighborCounting.PoincareNormalization.familyZero A T ≫ (b ▷ A.scheme))
          (Isogenies.NeighborCounting.PoincareNormalization.familyZero_naturality A a).symm (Isogenies.NeighborCounting.PoincareNormalization.familyZero_naturality A b).symm).hom) := by
  have hp := Picard.PoincareBundle.Line.Fibers.pullHom_eq (Picard.PoincareBundle.Line.Comparison.Bundle.fromShared L)
    (x := a ▷ A.scheme) (y := b ▷ A.scheme) e.hom (Isogenies.NeighborCounting.PoincareNormalization.familyZero A T)
    (Isogenies.NeighborCounting.PoincareNormalization.familyZero A T ≫ (a ▷ A.scheme)) (Isogenies.NeighborCounting.PoincareNormalization.familyZero A T ≫ (b ▷ A.scheme)) rfl rfl
  simp only [Picard.PoincareBundle.Line.Fibers.fiberPullbackIso, Scheme.Modules.pullbackCongr, eqToIso_refl, Iso.trans_refl] at hp
  have hnorm := fiberNormalization_iff (Scheme.Modules.pullback (Isogenies.NeighborCounting.PoincareNormalization.familyZero A T).left) e
    ((Scheme.Modules.pullbackComp (Isogenies.NeighborCounting.PoincareNormalization.familyZero A T).left (a ▷ A.scheme).left).app L.sheaf)
    ((Scheme.Modules.pullbackComp (Isogenies.NeighborCounting.PoincareNormalization.familyZero A T).left (b ▷ A.scheme).left).app L.sheaf)
    (familyZeroFiberFrame A a L eL) (familyZeroFiberFrame A b L eL)
  have ha := congrArg Iso.hom (familyPullbackZeroIso_eq_globalFrame A a L eL)
  have hb := congrArg (fun z => (Scheme.Modules.pullback (Isogenies.NeighborCounting.PoincareNormalization.familyZero A T).left).map e.hom ≫ z.hom)
    (familyPullbackZeroIso_eq_globalFrame A b L eL)
  constructor
  · intro he
    exact hp.trans (hnorm.mp (hb.symm.trans (he.trans ha)))
  · intro he
    exact hb.trans ((hnorm.mpr (hp.symm.trans he)).trans ha.symm)

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.FamilyZeroFrames.Construction
