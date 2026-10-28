import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.DisjointCoverAmpleness
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cartesian.PullbackAmpleness
import Mathlib.AlgebraicGeometry.Limits

/-! # Base Family Ampleness -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Ampleness after each member of a finite base-change family gives ampleness after the disjoint-union base change. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u v

theorem Line.Bundles.LineBundle.isAmple_baseChange_sigma
    {S X : Scheme.{u}} {ι : Type v} [Finite ι] [Small.{u} ι]
    (Y : ι → Scheme.{u}) (p : X ⟶ S) (f : ∀ i, Y i ⟶ S) (L : Line.Bundles.LineBundle X)
    (hL : ∀ i, (L.pullback (pullback.fst p (f i))).IsAmple) :
    (L.pullback (pullback.fst p (Sigma.desc f))).IsAmple := by
  let g := Sigma.desc f
  let a := pullback.fst p g
  let q := pullback.snd p g
  let T : ι → Scheme.{u} := fun i => Limits.pullback q (Sigma.ι Y i)
  let j : ∀ i, T i ⟶ Limits.pullback p g := fun i => pullback.fst q (Sigma.ι Y i)
  have hcover : ∀ x : (Limits.pullback p g : Scheme.{u}), ∃ i, x ∈ j i ''ᵁ (⊤ : (T i).Opens) := by
    intro x
    obtain ⟨y, hy⟩ := (sigmaOpenCover Y).covers (q x)
    let i := (sigmaOpenCover Y).idx (q x)
    obtain ⟨z, hz, _⟩ := Scheme.Pullback.exists_preimage_pullback x y hy.symm
    exact ⟨i, z, True.intro, hz⟩
  have hdis : Pairwise (fun i k => Disjoint (j i ''ᵁ (⊤ : (T i).Opens)) (j k ''ᵁ (⊤ : (T k).Opens))) := by
    intro i k hik
    change Disjoint ((pullback.fst q (Sigma.ι Y i)) ''ᵁ ⊤) ((pullback.fst q (Sigma.ι Y k)) ''ᵁ ⊤)
    rw [Scheme.Hom.image_top_eq_opensRange, Scheme.Hom.image_top_eq_opensRange,
      Scheme.Hom.opensRange_pullbackFst, Scheme.Hom.opensRange_pullbackFst]
    apply disjoint_iff.mpr
    rw [← Scheme.Hom.preimage_inf, disjoint_iff.mp (disjoint_opensRange_sigmaι Y i k hik),
      Scheme.Hom.preimage_bot]
  apply (L.pullback a).isAmple_of_finite_disjoint_open_cover T j hcover hdis
  intro i
  have H₀ : IsPullback (j i ≫ a) (pullback.snd q (Sigma.ι Y i)) p (Sigma.ι Y i ≫ g) :=
    ((IsPullback.of_hasPullback q (Sigma.ι Y i)).flip.paste_vert (IsPullback.of_hasPullback p g).flip).flip
  have H : IsPullback (j i ≫ a) (pullback.snd q (Sigma.ι Y i)) p (f i) :=
    (congrArg (fun r => IsPullback (j i ≫ a) (pullback.snd q (Sigma.ι Y i)) p r) (Sigma.ι_comp_desc f i)).mp H₀
  exact ((L.isAmple_pullback_iff_cartesian H).mpr (hL i)).of_iso
    ((Scheme.Modules.pullbackComp (j i) a).app L.sheaf).symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
