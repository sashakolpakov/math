import Mathlib.CategoryTheory.GlueData
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting

/-! # Mono Family Glue Data -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.MonoFamilyGlueData

noncomputable section

/-! Canonical gluing data for a family of monomorphisms into one ambient
object. Pairwise intersections are actual pullbacks. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v
variable {C : Type u} [Category.{v} C] [HasPullbacks C]
variable {J : Type v} {X : C} (U : J → C) (f : ∀ i, U i ⟶ X)

def monoFamilyTripleMap (i j k : J) :
    pullback (pullback.fst (f i) (f j)) (pullback.fst (f i) (f k)) ⟶
      pullback (pullback.fst (f j) (f k)) (pullback.fst (f j) (f i)) := by
  refine (pullbackRightPullbackFstIso _ _ _).hom ≫ ?_
  refine ?_ ≫ (pullbackSymmetry _ _).hom
  refine ?_ ≫ (pullbackRightPullbackFstIso _ _ _).inv
  refine pullback.map _ _ _ _ (pullbackSymmetry _ _).hom (𝟙 _) (𝟙 _) ?_ ?_
  · simp [pullback.condition]
  · simp

@[simp, reassoc]
theorem monoFamilyTripleMap_fst_fst (i j k : J) :
    monoFamilyTripleMap U f i j k ≫ pullback.fst _ _ ≫ pullback.fst _ _ =
      pullback.fst _ _ ≫ pullback.snd _ _ := by
  unfold monoFamilyTripleMap
  simp [pullback.map]
  rw [pullback.lift_fst_assoc]
  simp

@[simp, reassoc]
theorem monoFamilyTripleMap_fst_snd (i j k : J) :
    monoFamilyTripleMap U f i j k ≫ pullback.fst _ _ ≫ pullback.snd _ _ =
      pullback.snd _ _ ≫ pullback.snd _ _ := by
  unfold monoFamilyTripleMap
  simp [pullback.map]
  rw [pullback.lift_snd]
  simp

@[simp, reassoc]
theorem monoFamilyTripleMap_snd_fst (i j k : J) :
    monoFamilyTripleMap U f i j k ≫ pullback.snd _ _ ≫ pullback.fst _ _ =
      pullback.fst _ _ ≫ pullback.snd _ _ := by
  unfold monoFamilyTripleMap
  simp [pullback.map]
  rw [pullback.lift_fst_assoc]
  simp

@[simp, reassoc]
theorem monoFamilyTripleMap_snd_snd (i j k : J) :
    monoFamilyTripleMap U f i j k ≫ pullback.snd _ _ ≫ pullback.snd _ _ =
      pullback.fst _ _ ≫ pullback.fst _ _ := by
  unfold monoFamilyTripleMap
  simp [pullback.map]
  rw [pullback.lift_fst_assoc]
  simp

theorem monoFamilyTripleMap_cocycle (i j k : J) :
    monoFamilyTripleMap U f i j k ≫ monoFamilyTripleMap U f j k i ≫
      monoFamilyTripleMap U f k i j = 𝟙 _ := by
  apply pullback.hom_ext
  · apply pullback.hom_ext <;> simp
  · apply pullback.hom_ext <;> simp [pullback.condition]

def monoFamilyGlueData [∀ i, Mono (f i)] : GlueData C where
  J := J
  U := U
  V p := pullback (f p.1) (f p.2)
  f _ _ := pullback.fst _ _
  t _ _ := (pullbackSymmetry _ _).hom
  t_id _ := by simp
  t' := monoFamilyTripleMap U f
  t_fac i j k := by apply pullback.hom_ext <;> simp
  cocycle := monoFamilyTripleMap_cocycle U f

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.MonoFamilyGlueData
