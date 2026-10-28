import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Base
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations
import Mathlib.CategoryTheory.Monoidal.CommGrp_
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import Mathlib.AlgebraicGeometry.Limits

/-! # Components -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Components

noncomputable section

/-!
Component maps and their product are actual morphisms of schemes over the
arithmetic base. No H¹ comparison, model existence, component decomposition,
or generation property is stored as a field. The total map is constructed
from a supplied disjoint-union isomorphism, as in the conclusion of IntegralModel.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.MonObj

def RelativelyProjective {B : Scheme} (X : Over B) : Prop :=
  Nonempty (AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.ProjectivePresentation X)

/-- Forgetting the chosen relative dimension retains the actual group scheme. -/
def commutativeGroupOfAbelianScheme {B : Scheme} {g : ℕ}
    (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g B) : CommGrp (Over B) where
  X := A.scheme

/-- Componentwise schemes, commutative group schemes, sections, and maps.
All smoothness, properness, projectivity, and Albanese claims are conclusions. -/
structure ComponentAlbaneseData {B : Scheme} (T : Over B) (r : ℕ) where
  S : Fin r → Over B
  A : Fin r → CommGrp (Over B)
  x₀ : ∀ j, 𝟙_ (Over B) ⟶ S j
  a : ∀ j, S j ⟶ (A j).X

namespace ComponentAlbaneseData

variable {B : Scheme} {T : Over B} {r : ℕ} (D : ComponentAlbaneseData T r)

abbrev product : Over B := ∏ᶜ fun j => (D.A j).X

/-- The i-th source component maps to the j-th factor by aᵢ if i=j,
and by the group identity otherwise. -/
def coordinateMap (i j : Fin r) : D.S i ⟶ (D.A j).X :=
  if h : i = j then D.a i ≫ eqToHom (congrArg (fun k => (D.A k).X) h) else 1

@[simp] theorem coordinateMap_self (j : Fin r) : D.coordinateMap j j = D.a j := by
  simp [ComponentAlbaneseData.coordinateMap]

theorem coordinateMap_ne (i j : Fin r) (h : i ≠ j) : D.coordinateMap i j = 1 := by
  simp [ComponentAlbaneseData.coordinateMap, h]

def componentProductMap (i : Fin r) : D.S i ⟶ D.product :=
  Pi.lift (D.coordinateMap i)

/-- The total map is assembled from the component maps and the decomposition. -/
def totalMap (e : (∐ D.S) ≅ T) : T ⟶ D.product :=
  e.inv ≫ Sigma.desc D.componentProductMap

theorem totalMap_coordinate (e : (∐ D.S) ≅ T) (i j : Fin r) :
    Sigma.ι D.S i ≫ e.hom ≫ D.totalMap e ≫ Pi.π (fun k => (D.A k).X) j =
      D.coordinateMap i j := by
  simp [ComponentAlbaneseData.totalMap, ComponentAlbaneseData.componentProductMap]

theorem totalMap_self (e : (∐ D.S) ≅ T) (j : Fin r) :
    Sigma.ι D.S j ≫ e.hom ≫ D.totalMap e ≫ Pi.π (fun k => (D.A k).X) j = D.a j := by
  rw [D.totalMap_coordinate, D.coordinateMap_self]

/-- Genuine geometric-fiber points, written as morphisms over the base. -/
abbrev surfacePoints (j : Fin r) (t : Base.GeometricPoint B) :=
  Over.mk t.morphism ⟶ D.S j

abbrev abelianPoints (j : Fin r) (t : Base.GeometricPoint B) :=
  Additive (Over.mk t.morphism ⟶ (D.A j).X)

def mapOnPoints (j : Fin r) (t : Base.GeometricPoint B) :
    D.surfacePoints j t → D.abelianPoints j t :=
  fun x => Additive.ofMul (x ≫ D.a j)

def sumOfDifferences (j : Fin r) (n : ℕ) (t : Base.GeometricPoint B)
    (z : Fin n → D.surfacePoints j t × D.surfacePoints j t) :
    D.abelianPoints j t :=
  ∑ i, (D.mapOnPoints j t (z i).1 - D.mapOnPoints j t (z i).2)

abbrev complexSurface (c : Foundations.Scheme.ProjectiveSpace.complexBase ⟶ B) (j : Fin r) :
    Over Foundations.Scheme.ProjectiveSpace.complexBase := (Over.pullback c).obj (D.S j)

abbrev complexAbelian (c : Foundations.Scheme.ProjectiveSpace.complexBase ⟶ B) (j : Fin r) :
    CommGrp (Over Foundations.Scheme.ProjectiveSpace.complexBase) where
  X := (Over.pullback c).obj (D.A j).X
  grp := ((Over.pullback c).mapCommGrp.obj (D.A j)).grp
  comm := ((Over.pullback c).mapCommGrp.obj (D.A j)).comm

/-- The transparent wrapper retains exactly the canonical mapped group scheme. -/
theorem complexAbelian_eq_mapCommGrp (c : Foundations.Scheme.ProjectiveSpace.complexBase ⟶ B) (j : Fin r) :
    D.complexAbelian c j = (Over.pullback c).mapCommGrp.obj (D.A j) := rfl

/-- The base point is the pullback of the actual arithmetic section. -/
def complexBasePoint (c : Foundations.Scheme.ProjectiveSpace.complexBase ⟶ B) (j : Fin r) :
    𝟙_ (Over Foundations.Scheme.ProjectiveSpace.complexBase) ⟶ D.complexSurface c j :=
  (Functor.Monoidal.εIso (Over.pullback c)).hom ≫ (Over.pullback c).map (D.x₀ j)

/-- The component maps on complex fibers are defined by base change. -/
def complexMap (c : Foundations.Scheme.ProjectiveSpace.complexBase ⟶ B) (j : Fin r) :=
  (Over.pullback c).map (D.a j)

def totalComplexMap (c : Foundations.Scheme.ProjectiveSpace.complexBase ⟶ B) (e : (∐ D.S) ≅ T) :=
  (Over.pullback c).map (D.totalMap e)

/-- Base change preserves the actual product, with its canonical comparison. -/
def complexProductComparison (c : Foundations.Scheme.ProjectiveSpace.complexBase ⟶ B) :
    (Over.pullback c).obj D.product ≅
      ∏ᶜ fun j => (D.complexAbelian c j).X :=
  PreservesProduct.iso (Over.pullback c) (fun j => (D.A j).X)

/-- The ordinary Albanese universal property on the constructed complex fiber. -/
def IsComplexAlbanese (c : Foundations.Scheme.ProjectiveSpace.complexBase ⟶ B) (j : Fin r) : Prop :=
  letI : GrpObj ((Over.pullback c).obj (D.A j).X) :=
    (D.complexAbelian c j).grp
  D.complexBasePoint c j ≫ D.complexMap c j = 1 ∧
    ∀ (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
      (f : D.complexSurface c j ⟶ A.toOver),
      D.complexBasePoint c j ≫ f = 1 →
        ∃! φ : (D.complexAbelian c j).X ⟶ A.toOver,
          IsMonHom φ ∧ D.complexMap c j ≫ φ = f

/-- Compatibility of the total complex map is proved, not part of the data. -/
theorem totalComplexMap_self (c : Foundations.Scheme.ProjectiveSpace.complexBase ⟶ B)
    (e : (∐ D.S) ≅ T) (j : Fin r) :
    (Over.pullback c).map (Sigma.ι D.S j ≫ e.hom) ≫
      D.totalComplexMap c e ≫
      (Over.pullback c).map (Pi.π (fun k => (D.A k).X) j) = D.complexMap c j := by
  simp only [ComponentAlbaneseData.totalComplexMap, ComponentAlbaneseData.complexMap, ← Functor.map_comp]
  congr 1
  simpa only [Category.assoc] using D.totalMap_self e j

end ComponentAlbaneseData

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Components
