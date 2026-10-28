import Mathlib.Algebra.Category.Grp.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.NatIso
import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp

/-! # Ordinary Characters -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.OrdinaryCharacters.Construction

/-!
Characters of a split ordinary block. The annihilator of the first factor
consists exactly of characters of the second factor. The proof is made for
group-valued functors, so it applies simultaneously on all test schemes in
the Cartier-character sheaf; it is not a calculation on geometric points.
-/

open _root_.CategoryTheory
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u v w

variable {C : Type u} [Category.{v} C]

abbrev productGroupFunctor (G H : C ⥤ GrpCat.{w}) : C ⥤ GrpCat.{w} where
  obj X := GrpCat.of (G.obj X × H.obj X)
  map f := GrpCat.ofHom ((G.map f).hom.prodMap (H.map f).hom)
  map_id X := by ext x <;> simp
  map_comp f g := by ext x <;> simp

def firstFactorInclusion (G H : C ⥤ GrpCat.{w}) : G ⟶ productGroupFunctor G H where
  app X := GrpCat.ofHom {
    toFun x := (x, 1)
    map_one' := rfl
    map_mul' x y := by simp }
  naturality := by
    intro X Y f
    apply GrpCat.hom_ext
    apply MonoidHom.ext
    intro x
    change ((G.map f) x, 1) = ((G.map f) x, (H.map f) 1)
    exact Prod.ext rfl (H.map f).hom.map_one.symm

def secondFactorInclusion (G H : C ⥤ GrpCat.{w}) : H ⟶ productGroupFunctor G H where
  app X := GrpCat.ofHom {
    toFun x := (1, x)
    map_one' := rfl
    map_mul' x y := by simp }
  naturality := by
    intro X Y f
    apply GrpCat.hom_ext
    apply MonoidHom.ext
    intro x
    change (1, (H.map f) x) = ((G.map f) 1, (H.map f) x)
    exact Prod.ext (G.map f).hom.map_one.symm rfl

def secondFactorProjection (G H : C ⥤ GrpCat.{w}) : productGroupFunctor G H ⟶ H where
  app X := GrpCat.ofHom (MonoidHom.snd (G.obj X) (H.obj X))
  naturality := by intro X Y f; ext x; rfl

theorem secondFactorInclusion_projection (G H : C ⥤ GrpCat.{w}) :
    secondFactorInclusion G H ≫ secondFactorProjection G H = 𝟙 H := by
  ext X x
  rfl

theorem character_reconstruction
    (G H K : C ⥤ GrpCat.{w}) (χ : productGroupFunctor G H ⟶ K)
    (hχ : ∀ X (g : G.obj X), χ.app X (g, 1) = 1) :
    secondFactorProjection G H ≫ (secondFactorInclusion G H ≫ χ) = χ := by
  ext X x
  change χ.app X (1, x.2) = χ.app X x
  have hx : x = (x.1, 1) * (1, x.2) := by simp
  conv_rhs => rw [hx]
  rw [map_mul, hχ, one_mul]

/-- A character annihilating the first factor factors uniquely through the
second projection. This is the ordinary opposite-kernel calculation. -/
theorem character_factorization
    (G H K : C ⥤ GrpCat.{w}) (χ : productGroupFunctor G H ⟶ K)
    (hχ : ∀ X (g : G.obj X), χ.app X (g, 1) = 1) :
    ∃! ψ : H ⟶ K, secondFactorProjection G H ≫ ψ = χ := by
  refine ⟨secondFactorInclusion G H ≫ χ, character_reconstruction G H K χ hχ, ?_⟩
  intro ψ hψ
  have h := congrArg (fun t => secondFactorInclusion G H ≫ t) hψ
  simpa only [← Category.assoc, secondFactorInclusion_projection,
    Category.id_comp] using h

/-- The actual space of characters annihilating the multiplicative factor. -/
def AnnihilatorCharacters (G H K : C ⥤ GrpCat.{w}) :=
  {χ : productGroupFunctor G H ⟶ K // ∀ X (g : G.obj X), χ.app X (g, 1) = 1}

/-- The opposite annihilator is the character group of the quotient factor.
With Cartier duality this is the dual etale factor, hence multiplicative. -/
def annihilatorCharacterEquiv (G H K : C ⥤ GrpCat.{w}) :
    AnnihilatorCharacters G H K ≃ (H ⟶ K) where
  toFun χ := secondFactorInclusion G H ≫ χ.val
  invFun ψ := ⟨secondFactorProjection G H ≫ ψ, by
    intro X g
    change ψ.app X 1 = 1
    exact (ψ.app X).hom.map_one⟩
  left_inv χ := by
    apply Subtype.ext
    exact character_reconstruction G H K χ.val χ.property
  right_inv ψ := by
    change secondFactorInclusion G H ≫ (secondFactorProjection G H ≫ ψ) = ψ
    rw [← Category.assoc, secondFactorInclusion_projection, Category.id_comp]

variable [CartesianMonoidalCategory C] [BraidedCategory C]

/-- The split group-scheme product on an arbitrary test scheme has exactly
the expected product group of points. -/
def productPointEquiv (G H : Grp C) (X : C) :
    (X ⟶ (G ⊗ H).X) ≃* ((X ⟶ G.X) × (X ⟶ H.X)) where
  toFun a := (a ≫ fst G.X H.X, a ≫ snd G.X H.X)
  invFun a := lift a.1 a.2
  left_inv a := by
    apply CartesianMonoidalCategory.hom_ext <;> simp
  right_inv a := by simp
  map_mul' a b :=
    Prod.ext (MonObj.mul_comp a b (fst G.X H.X))
      (MonObj.mul_comp a b (snd G.X H.X))

/-- The product splitting is natural on all test schemes, so the preceding
annihilator calculation applies to native group-scheme character functors. -/
def productPointIso (G H : Grp C) :
    yonedaGrp.obj (G ⊗ H) ≅ productGroupFunctor (yonedaGrp.obj G) (yonedaGrp.obj H) :=
  NatIso.ofComponents (fun X => (productPointEquiv G H X.unop).toGrpIso) (by
    intro X Y f
    apply GrpCat.hom_ext
    apply MonoidHom.ext
    intro a
    exact Prod.ext (Category.assoc _ _ _) (Category.assoc _ _ _))

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.OrdinaryCharacters.Construction
