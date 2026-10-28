import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.OverOpenCoverGluing

/-! # Indexed Over Iso Gluing -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.IndexedOverIsoGluing

noncomputable section

section

/-! Compatible maps on an indexed family of actual open immersions
glue over the base, retaining their exact restrictions. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable {S : Scheme} {I : Type} (X : Over S) (A : I → Over S)
    (i : ∀ j, A j ⟶ X) [∀ j, IsOpenImmersion (i j).left]
    (hc : ∀ x : X.left, ∃ j, x ∈ (i j).left.opensRange)

def indexedOverOpenCover : X.left.OpenCover where
  I₀ := I
  X j := (A j).left
  f j := (i j).left
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    exact ⟨hc, fun j => inferInstance⟩

variable (Y : Over S) (f : ∀ j, A j ⟶ Y)
    (hf : ∀ j l, pullback.fst (i j).left (i l).left ≫ (f j).left =
      pullback.snd _ _ ≫ (f l).left)

def glueIndexedOverMap : X ⟶ Y :=
  OverOpenCoverGluing.glueOverOpenCover X Y (indexedOverOpenCover X A i hc) (fun j => (f j).left)
    (fun j => (f j).w.trans (i j).w.symm) hf

theorem glueIndexedOverMap_fac (j : I) : i j ≫ glueIndexedOverMap X A i hc Y f hf = f j := by
  apply Over.OverMorphism.ext
  exact OverOpenCoverGluing.glueOverOpenCover_fac X Y (indexedOverOpenCover X A i hc) (fun j => (f j).left)
    (fun j => (f j).w.trans (i j).w.symm) hf j

end

/-! Compatible local isomorphisms on actual source and target open
covers glue to a global isomorphism. Both composites are checked on the
original covers. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

attribute [local implicit_reducible] indexedOverOpenCover

variable {S : Scheme} {I : Type} (X Y : Over S) (A B : I → Over S)
    (i : ∀ j, A j ⟶ X) (j : ∀ l, B l ⟶ Y)
    [∀ l, IsOpenImmersion (i l).left] [∀ l, IsOpenImmersion (j l).left]
    (hX : ∀ x : X.left, ∃ l, x ∈ (i l).left.opensRange)
    (hY : ∀ y : Y.left, ∃ l, y ∈ (j l).left.opensRange)
    (e : ∀ l, A l ≅ B l)
    (hf : ∀ l m, pullback.fst (i l).left (i m).left ≫ ((e l).hom ≫ j l).left =
      pullback.snd _ _ ≫ ((e m).hom ≫ j m).left)
    (hg : ∀ l m, pullback.fst (j l).left (j m).left ≫ ((e l).inv ≫ i l).left =
      pullback.snd _ _ ≫ ((e m).inv ≫ i m).left)

def glueIndexedOverIso : X ≅ Y where
  hom := glueIndexedOverMap X A i hX Y (fun l => (e l).hom ≫ j l) hf
  inv := glueIndexedOverMap Y B j hY X (fun l => (e l).inv ≫ i l) hg
  hom_inv_id := by
    apply Over.OverMorphism.ext
    apply (indexedOverOpenCover X A i hX).hom_ext
    intro l
    have he : i l ≫
        (glueIndexedOverMap X A i hX Y (fun l => (e l).hom ≫ j l) hf ≫
          glueIndexedOverMap Y B j hY X (fun l => (e l).inv ≫ i l) hg) = i l ≫ 𝟙 X := by
      rw [← Category.assoc, glueIndexedOverMap_fac, Category.assoc, glueIndexedOverMap_fac,
        ← Category.assoc, (e l).hom_inv_id, Category.id_comp, Category.comp_id]
    exact congrArg Over.Hom.left he
  inv_hom_id := by
    apply Over.OverMorphism.ext
    apply (indexedOverOpenCover Y B j hY).hom_ext
    intro l
    have he : j l ≫
        (glueIndexedOverMap Y B j hY X (fun l => (e l).inv ≫ i l) hg ≫
          glueIndexedOverMap X A i hX Y (fun l => (e l).hom ≫ j l) hf) = j l ≫ 𝟙 Y := by
      rw [← Category.assoc, glueIndexedOverMap_fac, Category.assoc, glueIndexedOverMap_fac,
        ← Category.assoc, (e l).inv_hom_id, Category.id_comp, Category.comp_id]
    exact congrArg Over.Hom.left he

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.IndexedOverIsoGluing
