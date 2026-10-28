import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.BaseChange
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-! # Block Products -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.BlockProducts.Construction

noncomputable section

/-!
Finite products assemble chosen and opposite block subgroups into an
actual finite locally free closed subgroup. The source is built from the
block schemes, and the inclusion is the product of their embeddings.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

variable {S : Scheme.{u}}

def groupBlockProduct : (n : ℕ) → (Fin n → Grp (Over S)) → Grp (Over S)
  | 0, _ => Grp.trivial (Over S)
  | n + 1, B => B 0 ⊗ groupBlockProduct n (fun i => B i.succ)

def groupBlockProductMap : (n : ℕ) →
    (B C : Fin n → Grp (Over S)) → (∀ i, B i ⟶ C i) →
      (Construction.groupBlockProduct n B ⟶ Construction.groupBlockProduct n C)
  | 0, _, _, _ => 𝟙 (Grp.trivial (Over S))
  | n + 1, B, C, f => f 0 ⊗ₘ groupBlockProductMap n
      (fun i => B i.succ) (fun i => C i.succ) (fun i => f i.succ)

theorem groupBlockProduct_finiteLocallyFree (n : ℕ) (B : Fin n → Grp (Over S))
    (hB : ∀ i, IsFinite (B i).X.hom ∧ Flat (B i).X.hom ∧
      LocallyOfFinitePresentation (B i).X.hom) :
    IsFinite (Construction.groupBlockProduct n B).X.hom ∧
      Flat (Construction.groupBlockProduct n B).X.hom ∧
      LocallyOfFinitePresentation (Construction.groupBlockProduct n B).X.hom := by
  induction n with
  | zero =>
      change IsFinite (𝟙 S) ∧ Flat (𝟙 S) ∧ LocallyOfFinitePresentation (𝟙 S)
      exact ⟨inferInstance, inferInstance, inferInstance⟩
  | succ n ih =>
      let D := Construction.groupBlockProduct n (fun i => B i.succ)
      have hD := ih (fun i => B i.succ) (fun i => hB i.succ)
      have : IsFinite (B 0).X.hom := (hB 0).1
      have : Flat (B 0).X.hom := (hB 0).2.1
      have : LocallyOfFinitePresentation (B 0).X.hom := (hB 0).2.2
      have : IsFinite D.X.hom := hD.1
      have : Flat D.X.hom := hD.2.1
      have : LocallyOfFinitePresentation D.X.hom := hD.2.2
      change IsFinite (Limits.pullback.fst (B 0).X.hom D.X.hom ≫ (B 0).X.hom) ∧
        Flat (Limits.pullback.fst (B 0).X.hom D.X.hom ≫ (B 0).X.hom) ∧
        LocallyOfFinitePresentation (Limits.pullback.fst (B 0).X.hom D.X.hom ≫ (B 0).X.hom)
      exact ⟨inferInstance, inferInstance, inferInstance⟩

/-- Closed embeddings of the separate blocks assemble into a closed
embedding of their product, regardless of reducedness or characteristic. -/
theorem groupBlockProductMap_closed (n : ℕ) (B C : Fin n → Grp (Over S))
    (f : ∀ i, B i ⟶ C i) (hf : ∀ i, IsClosedImmersion (f i).hom.hom.left) :
    IsClosedImmersion (Construction.groupBlockProductMap n B C f).hom.hom.left := by
  induction n with
  | zero =>
      change IsClosedImmersion (𝟙 S)
      infer_instance
  | succ n ih =>
      let d := (Construction.groupBlockProductMap n (fun i => B i.succ) (fun i => C i.succ)
        (fun i => f i.succ)).hom.hom
      have hd : IsClosedImmersion d.left :=
        ih _ _ _ (fun i => hf i.succ)
      let : MorphismProperty.IsStableUnderComposition (@IsClosedImmersion.{u}) :=
        ⟨fun f g hf hg => by
          let := hf
          let := hg
          exact IsClosedImmersion.comp f g⟩
      change IsClosedImmersion ((f 0).hom.hom ⊗ₘ d).left
      rw [Over.tensorHom_left]
      exact MorphismProperty.pullbackMap (P := @IsClosedImmersion.{u}) (hf 0) hd
        (f 0).hom.hom.w.symm d.w.symm

/-- Transport the assembled subgroup from block coordinates into the
original torsion group scheme. -/
def fullBlockKernelInclusion (n : ℕ) (H B : Fin n → Grp (Over S))
    (i : ∀ v, H v ⟶ B v) (T : Grp (Over S)) (split : T ≅ Construction.groupBlockProduct n B) :
    Construction.groupBlockProduct n H ⟶ T := Construction.groupBlockProductMap n H B i ≫ split.inv

theorem fullBlockKernelInclusion_closed (n : ℕ) (H B : Fin n → Grp (Over S))
    (i : ∀ v, H v ⟶ B v) (hi : ∀ v, IsClosedImmersion (i v).hom.hom.left)
    (T : Grp (Over S)) (split : T ≅ Construction.groupBlockProduct n B) :
    IsClosedImmersion (fullBlockKernelInclusion n H B i T split).hom.hom.left := by
  have : IsClosedImmersion (Construction.groupBlockProductMap n H B i).hom.hom.left :=
    groupBlockProductMap_closed n H B i hi
  have : IsIso split.inv.hom.hom.left :=
    inferInstanceAs (IsIso (((Grp.forget (Over S)) ⋙ Over.forget S).map split.inv))
  change IsClosedImmersion ((Construction.groupBlockProductMap n H B i).hom.hom.left ≫ split.inv.hom.hom.left)
  infer_instance

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.BlockProducts.Construction
