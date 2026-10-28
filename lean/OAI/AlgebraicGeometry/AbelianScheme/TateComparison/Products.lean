import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.End
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Components
import Mathlib.CategoryTheory.Monoidal.Cartesian.GrpLimits

/-! # Products -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Products

noncomputable section

/-! The Albanese product is an actual commutative group scheme, constructed
from the component group schemes using the categorical product. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

variable {S : Scheme.{u}} {r : ℕ} (A : Fin r → CommGrp (Over S))

abbrev componentProductGroup : Grp (Over S) := ∏ᶜ fun j => (A j).toGrp

abbrev componentProductProjection (j : Fin r) :
    (componentProductGroup A).X ⟶ (A j).X :=
  (Pi.π (fun k => (A k).toGrp) j).hom.hom

theorem componentProduct_ext {T : Over S}
    (f g : T ⟶ (componentProductGroup A).X)
    (h : ∀ j, f ≫ componentProductProjection A j =
      g ≫ componentProductProjection A j) : f = g := by
  apply (isLimitOfPreserves (Grp.forget (Over S))
    (limit.isLimit (Discrete.functor fun j => (A j).toGrp))).hom_ext
  intro j
  exact h j.as

instance componentProduct_comm : IsCommMonObj (componentProductGroup A).X where
  mul_comm := by
    apply componentProduct_ext A
    intro j
    change (β_ _ _).hom ≫ μ ≫ componentProductProjection A j =
      μ ≫ componentProductProjection A j
    rw [IsMonHom.mul_hom, ← BraidedCategory.braiding_naturality_assoc,
      IsCommMonObj.mul_comm]

/-- The constructed product, with its inherited commutative group law. -/
abbrev componentProduct : CommGrp (Over S) := CommGrp.mk (componentProductGroup A).X

/-- The forgetful functor identifies this group product with the ordinary
scheme product used by IntegralModel's component-map construction. -/
def componentProductComparison :
    (componentProduct A).X ≅ ∏ᶜ fun j => (A j).X :=
  PreservesProduct.iso (Grp.forget (Over S)) (fun j => (A j).toGrp)

@[simp]
theorem componentProductComparison_projection (j : Fin r) :
    (componentProductComparison A).hom ≫ Pi.π (fun k => (A k).X) j =
      componentProductProjection A j := by
  exact piComparison_comp_π (Grp.forget (Over S)) (fun k => (A k).toGrp) j

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Products
