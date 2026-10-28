import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ConstantScheme.Iff
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-! # Constant Points Is -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.ConstantPointsIs.ConstantPoints

/-! Explicit point and base-change formulas for finite constant schemes. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ConstantScheme.Iff

variable {X Y T : Scheme.{u}} {I : Type u}

noncomputable def index (f : T ⟶ (AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme X I).left) : LocallyConstant T I :=
  (AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantSchemeIndex X I).comap ⟨f, f.continuous⟩

noncomputable def lift (a : T ⟶ X) (c : LocallyConstant T I) :
    T ⟶ (AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme X I).left :=
  (AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantSchemePointInverse (Over.mk a) c).left

@[simp, reassoc]
theorem lift_base (a : T ⟶ X) (c : LocallyConstant T I) :
    lift a c ≫ (AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme X I).hom = a :=
  (AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantSchemePointInverse (Over.mk a) c).w

@[simp]
theorem index_lift (a : T ⟶ X) (c : LocallyConstant T I) : index (lift a c) = c :=
  AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantSchemePoint_rightInverse (Over.mk a) c

theorem ext (f g : T ⟶ (AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme X I).left)
    (hb : f ≫ (AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme X I).hom = g ≫ (AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme X I).hom)
    (hi : index f = index g) : f = g := by
  let f' : Over.mk (f ≫ (AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme X I).hom) ⟶ AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme X I :=
    Over.homMk f rfl
  let g' : Over.mk (f ≫ (AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme X I).hom) ⟶ AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme X I :=
    Over.homMk g hb.symm
  have he : (AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantSchemePointsEquiv X I _) f' =
      (AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantSchemePointsEquiv X I _) g' := hi
  exact congrArg (fun k => k.left) ((AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantSchemePointsEquiv X I _).injective he)

@[simp]
theorem index_comp (f : T ⟶ Y) (g : Y ⟶ (AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme X I).left) :
    index (f ≫ g) = (index g).comap ⟨f, f.continuous⟩ := rfl

@[simp]
theorem index_ι_comp (f : T ⟶ X) (i : I) :
    index (f ≫ Sigma.ι (fun _ : I => X) i) = LocallyConstant.const T i := by
  apply LocallyConstant.ext
  intro x
  exact AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantSchemeIndex_ι i (f x)

noncomputable def map (f : X ⟶ Y) (I : Type u) :
    (AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme X I).left ⟶ (AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme Y I).left :=
  lift ((AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme X I).hom ≫ f) (AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantSchemeIndex X I)

@[simp, reassoc]
theorem map_base (f : X ⟶ Y) (I : Type u) :
    map f I ≫ (AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme Y I).hom = (AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme X I).hom ≫ f :=
  lift_base _ _

@[simp]
theorem index_map (f : X ⟶ Y) (I : Type u) :
    index (map f I) = AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantSchemeIndex X I := index_lift _ _

theorem isPullback (f : X ⟶ Y) (I : Type u) :
    IsPullback (map f I) (AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme X I).hom (AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme Y I).hom f := by
  apply IsPullback.mk'
  · exact map_base f I
  · intro Z a b hab hbase
    apply ConstantPoints.ext a b hbase
    have h := congrArg index hab
    rw [index_comp, index_comp, index_map] at h
    exact h
  · intro Z a b hab
    refine ⟨lift b (index a), ?_, lift_base _ _⟩
    apply ConstantPoints.ext
    · rw [Category.assoc, map_base, ← Category.assoc, lift_base]
      exact hab.symm
    · rw [index_comp, index_map]
      exact index_lift b (index a)

theorem field_factor (K : Type u) [Field K]
    (f : Spec (CommRingCat.of K) ⟶ (AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme X I).left) :
    ∃ i : I, f = (f ≫ (AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme X I).hom) ≫ Sigma.ι (fun _ : I => X) i := by
  let z : Spec (CommRingCat.of K) := default
  refine ⟨index f z, AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme_factor f (index f z) ?_⟩
  intro x
  exact congrArg (fun y => index f y) (Subsingleton.elim x z)

end OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.ConstantPointsIs.ConstantPoints
