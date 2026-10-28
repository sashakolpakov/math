import OAI.AlgebraicGeometry.Picard.PoincareBundle.Functor
import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp

/-! # Homogeneous -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Homogeneous

noncomputable section

/-!
# Homogeneous Picard pullback for PoincareBundle

Translation-invariant relative line classes form a presheaf. A morphism
of group schemes pulls these classes back functorially, so it induces
the contravariant map on the actual homogeneous Picard sheaves.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Functor

variable {S : Scheme.{u}} (A : Over S) [GrpObj A]

/-- Translation by a test-scheme point, with the test coordinate fixed. -/
def translation {T : Over S} (a : T ⟶ A) : T ⊗ A ⟶ T ⊗ A :=
  lift (fst T A) ((fst T A ≫ a) * snd T A)

/-- Homogeneity means that every translate after every test-scheme
base change has the same relative Picard class. -/
def IsHomogeneous (T : Over S) (q : (PoincareBundle.Functor.relativePicardPresheaf A).obj (op T)) : Prop :=
  ∀ (U : Over S) (h : U ⟶ T) (a : U ⟶ A),
    (PoincareBundle.Functor.toRelativePicard A).app (op U)
        (Line.Bundles.LineBundleClass.pullback (translation A a).left
          ((PoincareBundle.Functor.relativePicardPresheaf A).map h.op q)) =
      (PoincareBundle.Functor.toRelativePicard A).app (op U) ((PoincareBundle.Functor.relativePicardPresheaf A).map h.op q)

theorem IsHomogeneous.baseChange {T U : Over S}
    {q : (PoincareBundle.Functor.relativePicardPresheaf A).obj (op T)} (hq : IsHomogeneous A T q) (h : U ⟶ T) :
    IsHomogeneous A U ((PoincareBundle.Functor.relativePicardPresheaf A).map h.op q) := by
  intro V k a
  simpa only [op_comp, CategoryTheory.Functor.map_comp_apply] using hq V (k ≫ h) a

/-- The presheaf of actual homogeneous line-bundle classes. -/
def homogeneousPresheaf : (Over S)ᵒᵖ ⥤ Type (u + 1) where
  obj T := {q : (PoincareBundle.Functor.relativePicardPresheaf A).obj T // IsHomogeneous A T.unop q}
  map h := ↾(fun q => ⟨(PoincareBundle.Functor.relativePicardPresheaf A).map h q.val, q.property.baseChange A h.unop⟩)
  map_id T := by
    apply ConcreteCategory.ext_apply
    intro q
    apply Subtype.ext
    exact (PoincareBundle.Functor.relativePicardPresheaf A).map_id_apply T q.val
  map_comp h k := by
    apply ConcreteCategory.ext_apply
    intro q
    apply Subtype.ext
    exact (PoincareBundle.Functor.relativePicardPresheaf A).map_comp_apply h k q.val

/-- The fppf sheaf of homogeneous relative Picard classes. -/
def homogeneousSheaf : Sheaf (Scheme.fppfTopology.over S) (Type (u + 1)) :=
  (presheafToSheaf (Scheme.fppfTopology.over S) (Type (u + 1))).obj (homogeneousPresheaf A)

variable {A} {B : Over S} [GrpObj B] (f : A ⟶ B) [IsMonHom f]

/-- A group-scheme morphism commutes with translation by test points. -/
theorem translation_naturality {T : Over S} (a : T ⟶ A) :
    translation A a ≫ (𝟙 T ⊗ₘ f) = (𝟙 T ⊗ₘ f) ≫ translation B (a ≫ f) := by
  apply hom_ext <;> simp [translation, MonObj.mul_comp, MonObj.comp_mul, Category.assoc]

/-- The translation square commutes on the actual line-bundle classes. -/
theorem translation_pullback {T : Over S} (a : T ⟶ A)
    (q : Line.Bundles.LineBundleClass (T ⊗ B).left) :
    Line.Bundles.LineBundleClass.pullback (translation A a).left
        (Line.Bundles.LineBundleClass.pullback (PoincareBundle.Functor.familyMap f T) q) =
      Line.Bundles.LineBundleClass.pullback (PoincareBundle.Functor.familyMap f T)
        (Line.Bundles.LineBundleClass.pullback (translation B (a ≫ f)).left q) := by
  rw [← Line.Bundles.LineBundleClass.pullback_comp,
    ← Line.Bundles.LineBundleClass.pullback_comp]
  exact congrArg (fun b => Line.Bundles.LineBundleClass.pullback b q)
    (congrArg Over.Hom.left (translation_naturality f a))

/-- Pullback in the family variable preserves homogeneous classes. -/
theorem IsHomogeneous.pullback {T : Over S}
    {q : (PoincareBundle.Functor.relativePicardPresheaf B).obj (op T)} (hq : IsHomogeneous B T q) :
    IsHomogeneous A T ((PoincareBundle.Functor.pullbackPresheaf f).app (op T) q) := by
  intro U h a
  have hbase := (PoincareBundle.Functor.pullbackPresheaf f).naturality_apply h.op q
  have hη (z : (PoincareBundle.Functor.relativePicardPresheaf B).obj (op U)) :
      (PoincareBundle.Functor.pullbackSheaf f).hom.app (op U) ((PoincareBundle.Functor.toRelativePicard B).app (op U) z) =
        (PoincareBundle.Functor.toRelativePicard A).app (op U) ((PoincareBundle.Functor.pullbackPresheaf f).app (op U) z) :=
    congrArg (fun b => b.app (op U) z) (PoincareBundle.Functor.pullbackSheaf_toRelativePicard f)
  rw [← hbase]
  change (PoincareBundle.Functor.toRelativePicard A).app (op U)
      (Line.Bundles.LineBundleClass.pullback (translation A a).left
        (Line.Bundles.LineBundleClass.pullback (PoincareBundle.Functor.familyMap f U)
          ((PoincareBundle.Functor.relativePicardPresheaf B).map h.op q))) = _
  erw [translation_pullback f a]
  exact (hη _).symm.trans
    ((congrArg (fun z => (PoincareBundle.Functor.pullbackSheaf f).hom.app (op U) z) (hq U h (a ≫ f))).trans (hη _))

/-- Pullback on the presheaves of homogeneous classes. -/
def pullbackHomogeneousPresheaf : homogeneousPresheaf B ⟶ homogeneousPresheaf A where
  app T := ↾(fun q => ⟨(PoincareBundle.Functor.pullbackPresheaf f).app T q.val, q.property.pullback f⟩)
  naturality {T U} h := by
    apply ConcreteCategory.ext_apply
    intro q
    apply Subtype.ext
    exact (PoincareBundle.Functor.pullbackPresheaf f).naturality_apply h q.val

/-- The contravariant Picard map used to construct dual group-scheme maps. -/
def pullbackHomogeneousSheaf : homogeneousSheaf B ⟶ homogeneousSheaf A :=
  (presheafToSheaf (Scheme.fppfTopology.over S) (Type (u + 1))).map
    (pullbackHomogeneousPresheaf f)

@[simp]
theorem pullbackHomogeneousPresheaf_id :
    pullbackHomogeneousPresheaf (𝟙 A) = 𝟙 (homogeneousPresheaf A) := by
  apply NatTrans.ext
  funext T
  apply ConcreteCategory.ext_apply
  intro q
  apply Subtype.ext
  exact congrArg (fun b => b.app T q.val) (PoincareBundle.Functor.pullbackPresheaf_id (A := A))

theorem pullbackHomogeneousPresheaf_comp {C : Over S} [GrpObj C]
    (g : B ⟶ C) [IsMonHom g] :
    pullbackHomogeneousPresheaf (f ≫ g) =
      pullbackHomogeneousPresheaf g ≫ pullbackHomogeneousPresheaf f := by
  apply NatTrans.ext
  funext T
  apply ConcreteCategory.ext_apply
  intro q
  apply Subtype.ext
  exact congrArg (fun b => b.app T q.val) (PoincareBundle.Functor.pullbackPresheaf_comp f g)

@[simp]
theorem pullbackHomogeneousSheaf_id :
    pullbackHomogeneousSheaf (𝟙 A) = 𝟙 (homogeneousSheaf A) := by
  dsimp [pullbackHomogeneousSheaf]
  erw [pullbackHomogeneousPresheaf_id]
  exact (presheafToSheaf (Scheme.fppfTopology.over S) (Type (u + 1))).map_id _

theorem pullbackHomogeneousSheaf_comp {C : Over S} [GrpObj C]
    (g : B ⟶ C) [IsMonHom g] :
    pullbackHomogeneousSheaf (f ≫ g) =
      pullbackHomogeneousSheaf g ≫ pullbackHomogeneousSheaf f := by
  dsimp [pullbackHomogeneousSheaf]
  erw [pullbackHomogeneousPresheaf_comp, CategoryTheory.Functor.map_comp]
  rfl

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Homogeneous
