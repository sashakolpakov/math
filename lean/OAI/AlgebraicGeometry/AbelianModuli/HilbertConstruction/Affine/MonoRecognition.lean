import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Local.MorphismFactorization
import Mathlib.CategoryTheory.Comma.Over.Basic

/-! # Mono Recognition -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.MonoRecognition

noncomputable section

/-! Affine lifting properties determine actual scheme monomorphisms and their isomorphisms over a common target. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {S : Scheme.{u}} {M Z T W : Over S}

theorem overMono_lift_of_affine (j : Z ⟶ M) [Mono j] (x : T ⟶ M)
    (h : ∀ (R : CommRingCat.{u}) (f : Spec R ⟶ S) (a : Over.mk f ⟶ T),
      ∃ b : Over.mk f ⟶ Z, b ≫ j = a ≫ x) :
    ∃! g : T ⟶ Z, g ≫ j = x := by
  obtain ⟨g, hg, _⟩ := HilbertScheme.Presentations.Local.MorphismFactorization.lift_of_openCover T.left.affineOpenCover.openCover x.left j.left (by
    intro i
    change T.left.affineOpenCover.I₀ at i
    let a : Over.mk (T.left.affineOpenCover.f i ≫ T.hom) ⟶ T :=
      Over.homMk (T.left.affineOpenCover.f i)
    obtain ⟨b, hb⟩ := h (T.left.affineOpenCover.X i) _ a
    exact ⟨b.left, congrArg Over.Hom.left hb⟩)
  let l : T ⟶ Z := Over.homMk g (by
    rw [← j.w, ← Category.assoc, hg]
    exact x.w)
  have hl : l ≫ j = x := Over.OverMorphism.ext hg
  exact ⟨l, hl, fun k hk => (cancel_mono j).mp (hk.trans hl.symm)⟩

theorem overMono_iso_of_affine_lifts (j : Z ⟶ M) (k : W ⟶ M) [Mono j] [Mono k]
    (h : ∀ (R : CommRingCat.{u}) (f : Spec R ⟶ S) (x : Over.mk f ⟶ M),
      (∃ a : Over.mk f ⟶ Z, a ≫ j = x) ↔ (∃ b : Over.mk f ⟶ W, b ≫ k = x)) :
    ∃ e : Z ≅ W, e.hom ≫ k = j := by
  obtain ⟨g, hg, _⟩ := overMono_lift_of_affine k j (fun R f a => (h R f (a ≫ j)).mp ⟨a, rfl⟩)
  obtain ⟨l, hl, _⟩ := overMono_lift_of_affine j k (fun R f b => (h R f (b ≫ k)).mpr ⟨b, rfl⟩)
  have hgl : g ≫ l = 𝟙 Z := by
    apply (cancel_mono j).mp
    rw [Category.assoc, hl, hg, Category.id_comp]
  have hlg : l ≫ g = 𝟙 W := by
    apply (cancel_mono k).mp
    rw [Category.assoc, hg, hl, Category.id_comp]
  exact ⟨⟨g, l, hgl, hlg⟩, hg⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.MonoRecognition
