import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp

/-! # Group Tensor Iso -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GroupTensorIso.CM

noncomputable section

/-! Change a factor in a product of actual group objects through a
proved group isomorphism, preserving the native product group law. -/

open _root_.CategoryTheory MonoidalCategory CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u v
variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C] [BraidedCategory C]
  (N P Q : Grp C) (e : P ≅ Q)

def right : Grp.mk (N.X ⊗ P.X) ≅ Grp.mk (N.X ⊗ Q.X) := by
  let t : N.X ⊗ P.X ≅ N.X ⊗ Q.X := (Iso.refl N.X) ⊗ᵢ (Grp.forget C).mapIso e
  let : IsMonHom t.hom := by
    change IsMonHom ((𝟙 N.X) ⊗ₘ e.hom.hom.hom)
    infer_instance
  exact Grp.mkIso' (G := N.X ⊗ P.X) (H := N.X ⊗ Q.X) t

def left : Grp.mk (P.X ⊗ N.X) ≅ Grp.mk (Q.X ⊗ N.X) := by
  let t : P.X ⊗ N.X ≅ Q.X ⊗ N.X := (Grp.forget C).mapIso e ⊗ᵢ (Iso.refl N.X)
  let : IsMonHom t.hom := by
    change IsMonHom (e.hom.hom.hom ⊗ₘ (𝟙 N.X))
    infer_instance
  exact Grp.mkIso' (G := P.X ⊗ N.X) (H := Q.X ⊗ N.X) t

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GroupTensorIso.CM
