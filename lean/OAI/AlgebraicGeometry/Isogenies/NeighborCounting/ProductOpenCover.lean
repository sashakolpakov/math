import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PoincareNormalization
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.OpenImmersionGluing

/-! # Product Open Cover -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ProductOpenCover

noncomputable section

/-! Base change of disjoint open covers to product families, with the
original product sources and their native module comparisons retained. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory

universe u v

variable {S : Scheme.{u}} (P : Over S) {T U : Over S}

theorem productMap_isPullback (f : T ⟶ U) :
    IsPullback (f ▷ P).left (fst T P).left (fst U P).left f.left := by
  have hr : IsPullback (snd U P).left (fst U P).left P.hom U.hom :=
    (IsPullback.of_hasPullback U.hom P.hom).flip
  have ho : IsPullback ((f ▷ P).left ≫ (snd U P).left) (fst T P).left
      P.hom (f.left ≫ U.hom) := by
    have hs : (f ▷ P).left ≫ (snd U P).left = (snd T P).left :=
      congrArg Over.Hom.left (whiskerRight_snd f P)
    rw [hs, f.w]
    exact (IsPullback.of_hasPullback T.hom P.hom).flip
  exact IsPullback.of_right ho (congrArg Over.Hom.left (whiskerRight_fst f P)) hr

instance productMap_open (f : T ⟶ U) [IsOpenImmersion f.left] :
    IsOpenImmersion (f ▷ P).left :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (productMap_isPullback P f).flip (inferInstanceAs (IsOpenImmersion f.left))

instance productMap_flat (f : T ⟶ U) [Flat f.left] : Flat (f ▷ P).left :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (productMap_isPullback P f).flip (inferInstanceAs (Flat f.left))

instance productMap_surjective (f : T ⟶ U) [Surjective f.left] : Surjective (f ▷ P).left :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (productMap_isPullback P f).flip (inferInstanceAs (Surjective f.left))

instance productMap_quasiCompact (f : T ⟶ U) [QuasiCompact f.left] : QuasiCompact (f ▷ P).left :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (productMap_isPullback P f).flip (inferInstanceAs (QuasiCompact f.left))

variable {ι : Type v} (V : ι → Over S) (f : ∀ i, V i ⟶ T)
variable [∀ i, IsOpenImmersion (f i).left]

def productCover (hc : ∀ x : T.left, ∃ i, ∃ y : (V i).left, (f i).left y = x) :
    Scheme.OpenCover.{v} (T ⊗ P).left := by
  let C : Scheme.OpenCover.{v} T.left := Scheme.Cover.mkOfCovers ι
    (fun i ↦ (V i).left) (fun i ↦ (f i).left) hc
  exact Scheme.Cover.copy (C.pullback₁ (fst T P).left) ι
    (fun i ↦ (V i ⊗ P).left) (fun i ↦ (f i ▷ P).left) (Equiv.refl _)
    (fun i ↦ (productMap_isPullback P (f i)).isoPullback)
    (fun i ↦ (productMap_isPullback P (f i)).isoPullback_hom_fst.symm)

theorem productMap_disjoint
    (hd : Pairwise (fun i j ↦ Disjoint (f i).left.opensRange (f j).left.opensRange)) :
    Pairwise (fun i j ↦ Disjoint (f i ▷ P).left.opensRange (f j ▷ P).left.opensRange) := by
  intro i j hij W hWi hWj z hz
  obtain ⟨zi, hzi⟩ := hWi hz
  obtain ⟨zj, hzj⟩ := hWj hz
  have hi : (fst T P).left z ∈ (f i).left.opensRange :=
    ⟨(fst (V i) P).left zi,
      (congrArg (fun a ↦ a zi) (productMap_isPullback P (f i)).w).symm.trans
        (congrArg (fst T P).left hzi)⟩
  have hj : (fst T P).left z ∈ (f j).left.opensRange :=
    ⟨(fst (V j) P).left zj,
      (congrArg (fun a ↦ a zj) (productMap_isPullback P (f j)).w).symm.trans
        (congrArg (fst T P).left hzj)⟩
  have hs : Disjoint ((f i).left.opensRange : Set T.left) ((f j).left.opensRange : Set T.left) :=
    Set.disjoint_iff_inter_eq_empty.mpr (congrArg SetLike.coe (hd hij).eq_bot)
  exact Set.disjoint_left.mp hs hi hj

theorem existsUnique_disjoint_product_iso
    (hc : ∀ x : T.left, ∃ i, ∃ y : (V i).left, (f i).left y = x)
    (hd : Pairwise (fun i j ↦ Disjoint (f i).left.opensRange (f j).left.opensRange))
    {M N : (T ⊗ P).left.Modules}
    (e : ∀ i, (Scheme.Modules.pullback (f i ▷ P).left).obj M ≅
      (Scheme.Modules.pullback (f i ▷ P).left).obj N) :
    ∃! d : M ≅ N, ∀ i, (Scheme.Modules.pullback (f i ▷ P).left).mapIso d = e i :=
  OpenImmersionGluing.existsUnique_disjoint_immersion_iso
    (fun i ↦ (V i ⊗ P).left) (fun i ↦ (f i ▷ P).left)
    (productCover P V f hc).iSup_opensRange.ge (productMap_disjoint P V f hd) e

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ProductOpenCover
