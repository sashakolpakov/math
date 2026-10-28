import OAI.AlgebraicGeometry.Picard.PoincareBundle.Vertical.Homogeneity

/-! # Map -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Product.Map

noncomputable section

/-! The homogeneous Picard universal property constructs a map from an actual vertical product. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Functor OAI.AlgebraicGeometry.Picard.PoincareBundle.Homogeneous OAI.AlgebraicGeometry.Picard.PoincareBundle.Vertical.Homogeneity
open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers OAI.AlgebraicGeometry.Picard.PoincareBundle.Vertical.ProductParameters

variable {S : Scheme.{u}} {B A D : Over S} [GrpObj A]
  (R : Line.Bundles.LineBundle (B ⊗ A).left)
  (β : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap (Line.Fibers.fiber R (Vertical.ProductParameters.inputLeft B A)) (Line.Fibers.fiber R (Vertical.ProductParameters.inputRight B A))
    (Line.Fibers.fiber R (Vertical.ProductParameters.outputPoint B A)))
  (hβ : IsIso (Bilinear.BilinearPullback.toHom β))

/-- The constructed family fiber, together with its proved homogeneity. -/
def homogeneousClass {T : Over S} (x : T ⟶ B) : (Homogeneous.homogeneousPresheaf A).obj (op T) :=
  ⟨Vertical.Homogeneity.familyClass R x, Vertical.Homogeneity.familyClass_isHomogeneous R β hβ x⟩

theorem homogeneousClass_natural {T U : Over S} (h : U ⟶ T) (x : T ⟶ B) :
    (Homogeneous.homogeneousPresheaf A).map h.op (homogeneousClass R β hβ x) =
      homogeneousClass R β hβ (h ≫ x) := by
  apply Subtype.ext
  exact Vertical.Homogeneity.familyClass_natural R h x

/-- The actual homogeneous relative Picard section of a family fiber. -/
def sectionClass {T : Over S} (x : T ⟶ B) : (Homogeneous.homogeneousSheaf A).obj.obj (op T) :=
  (toSheafify (Scheme.fppfTopology.over S) (Homogeneous.homogeneousPresheaf A)).app (op T)
    (homogeneousClass R β hβ x)

theorem sectionClass_natural {T U : Over S} (h : U ⟶ T) (x : T ⟶ B) :
    (Homogeneous.homogeneousSheaf A).obj.map h.op (sectionClass R β hβ x) =
      sectionClass R β hβ (h ≫ x) := by
  dsimp only [sectionClass]
  erw [← (toSheafify (Scheme.fppfTopology.over S) (Homogeneous.homogeneousPresheaf A)).naturality_apply,
    homogeneousClass_natural]

variable (HD : (Homogeneous.homogeneousSheaf A).obj.RepresentableBy D)

/-- The genuine Picard universal property constructs the represented family map. -/
def representedMap : B ⟶ D := HD.homEquiv.symm (sectionClass R β hβ (𝟙 B))

/-- The constructed map represents every actual family fiber. -/
theorem representedMap_action {T : Over S} (x : T ⟶ B) :
    HD.homEquiv (x ≫ representedMap R β hβ HD) = sectionClass R β hβ x := by
  rw [HD.homEquiv_comp]
  dsimp only [representedMap]
  rw [Equiv.apply_symm_apply, sectionClass_natural, Category.comp_id]

/-- Representation determines the constructed family map uniquely. -/
theorem representedMap_unique (m : B ⟶ D)
    (hm : ∀ (T : Over S) (x : T ⟶ B), HD.homEquiv (x ≫ m) = sectionClass R β hβ x) :
    m = representedMap R β hβ HD := by
  apply HD.homEquiv.injective
  have hh : HD.homEquiv m = sectionClass R β hβ (𝟙 B) := by
    simpa only [Category.id_comp] using hm B (𝟙 B)
  exact hh.trans (Equiv.apply_symm_apply _ _).symm

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Product.Map
