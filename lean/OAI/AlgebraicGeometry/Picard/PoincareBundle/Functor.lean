import OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Bundles
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.CategoryTheory.Sites.Over
import Mathlib.CategoryTheory.Sites.LeftExact
import Mathlib.CategoryTheory.Monoidal.Cartesian.Over

/-! # Functor -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Functor

noncomputable section

/-!
# Relative Picard pullback for PoincareBundle

The relative Picard sheaf is the fppf sheafification of actual line-bundle
classes on test-scheme base changes. Pullback in the family variable is
constructed from geometric pullback and proved functorial.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory

universe u

variable {S : Scheme.{u}}

/-- The total spaces obtained by changing the test scheme of a family. -/
def familySchemeFunctor (A : Over S) : Over S ⥤ Scheme.{u} :=
  tensorRight A ⋙ Over.forget S

/-- Actual line-bundle classes on the base changes of a family. -/
def relativePicardPresheaf (A : Over S) : (Over S)ᵒᵖ ⥤ Type (u + 1) :=
  (familySchemeFunctor A).op ⋙ Line.Bundles.lineBundleClassFunctor

/-- The relative fppf Picard sheaf. -/
def relativePicardSheaf (A : Over S) :
    Sheaf (Scheme.fppfTopology.over S) (Type (u + 1)) :=
  (presheafToSheaf (Scheme.fppfTopology.over S) (Type (u + 1))).obj
    (relativePicardPresheaf A)

/-- Actual line classes map into the relative Picard sheaf. -/
def toRelativePicard (A : Over S) : relativePicardPresheaf A ⟶ (relativePicardSheaf A).obj :=
  toSheafify (Scheme.fppfTopology.over S) (relativePicardPresheaf A)

variable {A B C : Over S}

/-- The map between two base-changed families at the test scheme T. -/
def familyMap (f : A ⟶ B) (T : Over S) : (T ⊗ A).left ⟶ (T ⊗ B).left :=
  (𝟙 T ⊗ₘ f).left

/-- Changing the test scheme commutes with the map of families. -/
theorem familyMap_naturality (f : A ⟶ B) {T U : Over S} (a : U ⟶ T) :
    familyMap f U ≫ (familySchemeFunctor B).map a =
      (familySchemeFunctor A).map a ≫ familyMap f T := by
  change ((𝟙 U ⊗ₘ f) ≫ (a ⊗ₘ 𝟙 B)).left = ((a ⊗ₘ 𝟙 A) ≫ (𝟙 T ⊗ₘ f)).left
  rw [tensorHom_comp_tensorHom, tensorHom_comp_tensorHom]
  simp

/-- Pullback of relative line classes by a morphism of families. -/
def pullbackPresheaf (f : A ⟶ B) : relativePicardPresheaf B ⟶ relativePicardPresheaf A where
  app T := ↾(Line.Bundles.LineBundleClass.pullback (familyMap f T.unop))
  naturality {T U} a := by
    ext q
    change Line.Bundles.LineBundleClass.pullback (familyMap f U.unop)
        (Line.Bundles.LineBundleClass.pullback ((familySchemeFunctor B).map a.unop) q) =
      Line.Bundles.LineBundleClass.pullback ((familySchemeFunctor A).map a.unop)
        (Line.Bundles.LineBundleClass.pullback (familyMap f T.unop) q)
    erw [← Line.Bundles.LineBundleClass.pullback_comp,
      ← Line.Bundles.LineBundleClass.pullback_comp, familyMap_naturality]
    rfl

@[simp]
theorem familyMap_id (T : Over S) : familyMap (𝟙 A) T = 𝟙 (T ⊗ A).left := by
  change (𝟙 T ⊗ₘ 𝟙 A).left = (𝟙 (T ⊗ A) : T ⊗ A ⟶ T ⊗ A).left
  simp

theorem familyMap_comp (f : A ⟶ B) (g : B ⟶ C) (T : Over S) :
    familyMap (f ≫ g) T = familyMap f T ≫ familyMap g T := by
  change (𝟙 T ⊗ₘ (f ≫ g)).left = ((𝟙 T ⊗ₘ f) ≫ (𝟙 T ⊗ₘ g)).left
  rw [tensorHom_comp_tensorHom, Category.id_comp]

@[simp]
theorem pullbackPresheaf_id : pullbackPresheaf (𝟙 A) = 𝟙 (relativePicardPresheaf A) := by
  ext T q
  change Line.Bundles.LineBundleClass.pullback (familyMap (𝟙 A) T.unop) q = q
  erw [familyMap_id, Line.Bundles.LineBundleClass.pullback_id]

theorem pullbackPresheaf_comp (f : A ⟶ B) (g : B ⟶ C) :
    pullbackPresheaf (f ≫ g) = pullbackPresheaf g ≫ pullbackPresheaf f := by
  ext T q
  change Line.Bundles.LineBundleClass.pullback (familyMap (f ≫ g) T.unop) q = _
  erw [familyMap_comp, Line.Bundles.LineBundleClass.pullback_comp]
  rfl

/-- Pullback of the actual relative Picard sheaves. -/
def pullbackSheaf (f : A ⟶ B) : relativePicardSheaf B ⟶ relativePicardSheaf A :=
  (presheafToSheaf (Scheme.fppfTopology.over S) (Type (u + 1))).map (pullbackPresheaf f)

/-- Geometric pullback and the map to the Picard sheaf agree. -/
theorem pullbackSheaf_toRelativePicard (f : A ⟶ B) :
    toRelativePicard B ≫ (pullbackSheaf f).hom = pullbackPresheaf f ≫ toRelativePicard A :=
  (toSheafify_naturality _ (pullbackPresheaf f)).symm

@[simp]
theorem pullbackSheaf_id : pullbackSheaf (𝟙 A) = 𝟙 (relativePicardSheaf A) := by
  dsimp [pullbackSheaf]
  erw [pullbackPresheaf_id]
  exact (presheafToSheaf (Scheme.fppfTopology.over S) (Type (u + 1))).map_id _

theorem pullbackSheaf_comp (f : A ⟶ B) (g : B ⟶ C) :
    pullbackSheaf (f ≫ g) = pullbackSheaf g ≫ pullbackSheaf f := by
  dsimp [pullbackSheaf]
  erw [pullbackPresheaf_comp, CategoryTheory.Functor.map_comp]
  rfl

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Functor
