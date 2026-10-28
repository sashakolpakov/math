import OAI.NumberTheory.PadicHodge.GeometricComparison.Affine.OpenProducts

/-! # Map Pairs -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Affine.MapPairs.AffineMapPairs

noncomputable section

/-! Compatible affine source and target opens form an intersection
semilattice for an arbitrary scheme morphism. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {X Y : Scheme.{0}} (f : X ⟶ Y)

abbrev Charts := {P : X.affineOpens × Y.affineOpens // P.1.val ≤ f ⁻¹ᵁ P.2.val}

def source : Charts f ⥤ X.affineOpens where
  obj P := P.val.1
  map a := homOfLE (leOfHom a).1

def target : Charts f ⥤ Y.affineOpens where
  obj P := P.val.2
  map a := homOfLE (leOfHom a).2

theorem compatible (P : Charts f) : ((source f).obj P).val ≤ f ⁻¹ᵁ ((target f).obj P).val :=
  P.property

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

end OAI.NumberTheory.PadicHodge.GeometricComparison.Affine.MapPairs.AffineMapPairs
