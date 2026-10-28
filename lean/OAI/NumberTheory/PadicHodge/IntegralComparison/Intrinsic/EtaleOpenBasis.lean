import OAI.NumberTheory.PadicHodge.IntegralComparison.FiniteEtale.TraceBasis

/-! # Etale Open Basis -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Intrinsic.EtaleOpenBasis

noncomputable section

/-! Affine opens carrying actual étale coordinates form a basis on a
smooth proper model. The coordinate choices retain their original
section algebras. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
universe u
variable (R : Type u) [CommRing R] (X : Over (Spec (CommRingCat.of R)))

def Good (U : X.left.Opens) : Prop :=
  IsAffineOpen U ∧ FiniteEtale.TraceBasis.HasCoordinates R X U
abbrev Index := {U : X.left.Opens // Good R X U}
abbrev opens (a : Index R X) : X.left.Opens := a.val
abbrev affine (a : Index R X) : X.left.affineOpens := ⟨a.val, a.property.1⟩
abbrev ring (a : Index R X) := IntrinsicDeRham.SectionUnit.Intrinsic.ring R X a.val

def coordinateIndex (a : Index R X) : Type u := a.property.2.choose
instance coordinateFintype (a : Index R X) : Fintype (coordinateIndex R X a) :=
  a.property.2.choose_spec.choose
instance polynomialAlgebra (a : Index R X) :
    Algebra (MvPolynomial (coordinateIndex R X a) R) (ring R X a) :=
  a.property.2.choose_spec.choose_spec.choose
instance coordinateTower (a : Index R X) :
    IsScalarTower R (MvPolynomial (coordinateIndex R X a) R) (ring R X a) :=
  a.property.2.choose_spec.choose_spec.choose_spec.1
instance coordinateEtale (a : Index R X) :
    Algebra.Etale (MvPolynomial (coordinateIndex R X a) R) (ring R X a) :=
  a.property.2.choose_spec.choose_spec.choose_spec.2

@[instance_reducible] def coordinateOrder (a : Index R X) : LinearOrder (coordinateIndex R X a) :=
  LinearOrder.lift' (Fintype.equivFin _) (Fintype.equivFin _).injective

variable [IsProper X.hom] [Smooth X.hom]

theorem neighborhood (U : X.left.Opens) (x : X.left) (hx : x ∈ U) :
    ∃ a : Index R X, x ∈ opens R X a ∧ opens R X a ≤ U := by
  let : IsFinite ((𝟙 X : X ⟶ X).left) := by
    change IsFinite (𝟙 X.left)
    infer_instance
  let : Etale ((𝟙 X : X ⟶ X).left) := by
    change Etale (𝟙 X.left)
    infer_instance
  obtain ⟨a, ha, hU⟩ := FiniteEtale.TraceBasis.neighborhood R X X (𝟙 X) U x hx
  exact ⟨⟨a.val, a.property.1, a.property.2.1⟩, ha, hU⟩

theorem isBasis : Opens.IsBasis (Set.range (opens R X)) := by
  apply Opens.isBasis_iff_nbhd.mpr
  intro U x hx
  obtain ⟨a, ha, hU⟩ := neighborhood R X U x hx
  exact ⟨opens R X a, ⟨a,rfl⟩, ha, hU⟩

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Intrinsic.EtaleOpenBasis
