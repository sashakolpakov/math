import OAI.NumberTheory.PadicHodge.GeometricComparison.Affine.OpenProducts

/-! # Morphism Pairs -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.Affine.MorphismPairs.AffineMorphismPairs

noncomputable section

/-! Compatible affine chart pairs form an intersection category for scheme morphisms in every universe. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u
variable {X Y : Scheme.{u}} (f : X ⟶ Y)
abbrev Charts := {P : X.affineOpens × Y.affineOpens // P.1.val ≤ f ⁻¹ᵁ P.2.val}
def source : Charts f ⥤ X.affineOpens where
  obj P := P.val.1
  map a := homOfLE (leOfHom a).1
def target : Charts f ⥤ Y.affineOpens where
  obj P := P.val.2
  map a := homOfLE (leOfHom a).2

variable [X.IsSeparated] [Y.IsSeparated]
instance semilatticeInf : SemilatticeInf (Charts f) where
  inf P Q := ⟨(P.val.1 ⊓ Q.val.1, P.val.2 ⊓ Q.val.2), by
    intro x hx
    exact ⟨P.property hx.1, Q.property hx.2⟩⟩
  inf_le_left _ _ := ⟨inf_le_left, inf_le_left⟩
  inf_le_right _ _ := ⟨inf_le_right, inf_le_right⟩
  le_inf _ _ _ h₁ h₂ := ⟨le_inf h₁.1 h₂.1, le_inf h₁.2 h₂.2⟩
theorem source_inf (P Q : Charts f) : (source f).obj (P ⊓ Q) = (source f).obj P ⊓ (source f).obj Q := rfl
theorem target_inf (P Q : Charts f) : (target f).obj (P ⊓ Q) = (target f).obj P ⊓ (target f).obj Q := rfl

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.Affine.MorphismPairs.AffineMorphismPairs
