import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback

/-! # Pair Cech Maps -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Kernel.PairCechMaps.Construction.KernelPairDescent

noncomputable section

/-! The actual kernel pair and composable pairs of a single cover,
with their universal maps from arbitrary test objects. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v
variable {C : Type u} [Category.{v} C] [HasPullbacks C] {X Y : C} (f : X ⟶ Y)

abbrev Relation := pullback f f
abbrev Triple := pullback (pullback.snd f f) (pullback.fst f f)
abbrev first : Triple f ⟶ Relation f := pullback.fst _ _
abbrev second : Triple f ⟶ Relation f := pullback.snd _ _
abbrev source : Triple f ⟶ X := first f ≫ pullback.fst f f
abbrev middle : Triple f ⟶ X := first f ≫ pullback.snd f f
abbrev target : Triple f ⟶ X := second f ≫ pullback.snd f f

theorem second_middle : second f ≫ pullback.fst f f = middle f := pullback.condition.symm

def outer : Triple f ⟶ Relation f :=
  pullback.lift (source f) (target f) (by
    change (first f ≫ pullback.fst f f) ≫ f = (second f ≫ pullback.snd f f) ≫ f
    calc
      _ = (first f ≫ pullback.snd f f) ≫ f := by rw [Category.assoc, pullback.condition, ← Category.assoc]
      _ = (second f ≫ pullback.fst f f) ≫ f := congrArg (fun k => k ≫ f) pullback.condition
      _ = _ := by rw [Category.assoc, pullback.condition, ← Category.assoc])

theorem outer_source : outer f ≫ pullback.fst f f = source f := pullback.lift_fst _ _ _
theorem outer_target : outer f ≫ pullback.snd f f = target f := pullback.lift_snd _ _ _

def diagonal : X ⟶ Relation f := pullback.lift (𝟙 X) (𝟙 X) rfl
theorem diagonal_fst : diagonal f ≫ pullback.fst f f = 𝟙 X := pullback.lift_fst _ _ _
theorem diagonal_snd : diagonal f ≫ pullback.snd f f = 𝟙 X := pullback.lift_snd _ _ _

def pair {T : C} (x y : T ⟶ X) (h : x ≫ f = y ≫ f) : T ⟶ Relation f := pullback.lift x y h
theorem pair_fst {T : C} (x y : T ⟶ X) (h : x ≫ f = y ≫ f) :
    pair f x y h ≫ pullback.fst f f = x := pullback.lift_fst _ _ _
theorem pair_snd {T : C} (x y : T ⟶ X) (h : x ≫ f = y ≫ f) :
    pair f x y h ≫ pullback.snd f f = y := pullback.lift_snd _ _ _

theorem pair_self {T : C} (x : T ⟶ X) : pair f x x rfl = x ≫ diagonal f := by
  apply pullback.hom_ext
  · rw [pair_fst, Category.assoc, diagonal_fst, Category.comp_id]
  · rw [pair_snd, Category.assoc, diagonal_snd, Category.comp_id]

theorem pair_natural {T U : C} (g : U ⟶ T) (x y : T ⟶ X) (h : x ≫ f = y ≫ f)
    (x' y' : U ⟶ X) (h' : x' ≫ f = y' ≫ f) (hx : g ≫ x = x') (hy : g ≫ y = y') :
    g ≫ pair f x y h = pair f x' y' h' := by
  apply pullback.hom_ext
  · rw [Category.assoc, pair_fst, pair_fst, hx]
  · rw [Category.assoc, pair_snd, pair_snd, hy]

def triple {T : C} (x y z : T ⟶ X) (hxy : x ≫ f = y ≫ f) (hyz : y ≫ f = z ≫ f) :
    T ⟶ Triple f :=
  pullback.lift (pair f x y hxy) (pair f y z hyz) (by rw [pair_snd, pair_fst])

theorem triple_first {T : C} (x y z : T ⟶ X) (hxy : x ≫ f = y ≫ f) (hyz : y ≫ f = z ≫ f) :
    triple f x y z hxy hyz ≫ first f = pair f x y hxy := pullback.lift_fst _ _ _
theorem triple_second {T : C} (x y z : T ⟶ X) (hxy : x ≫ f = y ≫ f) (hyz : y ≫ f = z ≫ f) :
    triple f x y z hxy hyz ≫ second f = pair f y z hyz := pullback.lift_snd _ _ _
theorem triple_outer {T : C} (x y z : T ⟶ X) (hxy : x ≫ f = y ≫ f) (hyz : y ≫ f = z ≫ f) :
    triple f x y z hxy hyz ≫ outer f = pair f x z (hxy.trans hyz) := by
  apply pullback.hom_ext
  · rw [Category.assoc, outer_source, pair_fst]
    change triple f x y z hxy hyz ≫ first f ≫ pullback.fst f f = x
    rw [← Category.assoc, triple_first, pair_fst]
  · rw [Category.assoc, outer_target, pair_snd]
    change triple f x y z hxy hyz ≫ second f ≫ pullback.snd f f = z
    rw [← Category.assoc, triple_second, pair_snd]

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Kernel.PairCechMaps.Construction.KernelPairDescent
