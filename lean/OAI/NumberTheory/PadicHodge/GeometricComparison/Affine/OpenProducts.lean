import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.CategoryTheory.Limits.Preorder
import OAI.NumberTheory.PadicHodge.IntegralComparison.NonemptyCechNerve

/-! # Open Products -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Affine.OpenProducts.AffineOpenProducts

noncomputable section

/-! Affine opens of a separated scheme have the nonempty intersections needed
for the original Čech tuple construction. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u
variable (X : Scheme.{u}) [X.IsSeparated]

instance semilatticeInf : SemilatticeInf X.affineOpens where
  __ := (inferInstance : PartialOrder X.affineOpens)
  inf U V := ⟨U.val ⊓ V.val, U.property.inf V.property⟩
  inf_le_left U V := (show U.val ⊓ V.val ≤ U.val from inf_le_left)
  inf_le_right U V := (show U.val ⊓ V.val ≤ V.val from inf_le_right)
  le_inf U V T hUV hUT := (show U.val ≤ V.val ⊓ T.val from le_inf hUV hUT)

def inclusion : X.affineOpens ⥤ X.Opens where
  obj U := U.val
  map α := homOfLE (leOfHom α)

theorem product_eq {ι : Type u} [Finite ι] [Nonempty ι]
    (U : ι → X.affineOpens) [HasProduct U] :
    (∏ᶜ U).val = ⨅ i, (U i).val := by
  apply le_antisymm
  · exact le_iInf fun i => leOfHom (Pi.π U i)
  · let V : X.affineOpens := ⟨⨅ i, (U i).val, IsAffineOpen.iInf (fun i => (U i).property)⟩
    exact leOfHom (Pi.lift (P := V) (fun i => homOfLE (iInf_le (fun j => (U j).val) i)))

def nerve {ι : Type u} (U : ι → X.affineOpens) :
    SimplicialObject (FormalCoproduct.{u} X.affineOpens) :=
  IntegralComparison.NonemptyCechNerve.nerve U

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Affine.OpenProducts.AffineOpenProducts
