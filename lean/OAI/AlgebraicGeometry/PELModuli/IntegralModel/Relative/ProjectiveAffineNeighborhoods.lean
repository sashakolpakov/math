import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Projective.Neighborhoods

/-! # Projective Affine Neighborhoods -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Relative.ProjectiveAffineNeighborhoods

noncomputable section

/-! Over an algebra over an infinite field, finite sets in projective
space have affine neighborhoods. Coefficients are chosen in the field;
the points may have arbitrary residue fields over the coefficient ring. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.ArithmeticGeometry.Models.SpreadingOut.Projective.Construction.ProjectiveConstruction

variable {K R : Type} [Field K] [Infinite K] [CommRing R] [Algebra K R]

include K in
theorem relative_projective_finite_set_affine_neighborhood (n : ℕ)
    (F : Set (ArithmeticGeometry.Models.SpreadingOut.Projective.Construction.ProjectiveConstruction.projectiveSpace (K := R) n)) (hF : F.Finite) :
    ∃ U : (ArithmeticGeometry.Models.SpreadingOut.Projective.Construction.ProjectiveConstruction.projectiveSpace (K := R) n).Opens, IsAffineOpen U ∧ F ⊆ U := by
  classical
  have : Finite F := hF.to_subtype
  let V := (ArithmeticGeometry.Models.SpreadingOut.Projective.Construction.ProjectiveConstruction.projectiveGrading (K := R) n 1).restrictScalars K
  let p (x : F) : Submodule K V :=
    ((x.val.asHomogeneousIdeal.toIdeal).restrictScalars K).comap V.subtype
  have hp (x : F) : p x ≠ ⊤ := by
    obtain ⟨i, hi⟩ := ArithmeticGeometry.Models.SpreadingOut.Projective.Construction.ProjectiveConstruction.exists_mem_projectiveCoordinateOpen n x.val
    have hn : MvPolynomial.X i ∉ x.val.asHomogeneousIdeal :=
      (ArithmeticGeometry.Models.SpreadingOut.Projective.Construction.ProjectiveConstruction.mem_projectiveCoordinateOpen n i x.val).mp hi
    intro htop
    let v : V := ⟨MvPolynomial.X i, MvPolynomial.isHomogeneous_X R i⟩
    have hv : v ∈ p x := htop ▸ Submodule.mem_top
    exact hn hv
  obtain ⟨l, hl⟩ := Submodule.exists_forall_notMem_of_forall_ne_top p hp
  refine ⟨Proj.basicOpen (ArithmeticGeometry.Models.SpreadingOut.Projective.Construction.ProjectiveConstruction.projectiveGrading (K := R) n) l.val,
    Proj.isAffineOpen_basicOpen _ _ l.property Nat.zero_lt_one, ?_⟩
  intro x hx
  exact (Proj.mem_basicOpen _ _ x).mpr (hl ⟨x, hx⟩)

include K in
theorem finite_set_affine_neighborhood_of_relative_projective_embedding
    {X : Scheme.{0}} (n : ℕ) (i : X ⟶ ArithmeticGeometry.Models.SpreadingOut.Projective.Construction.ProjectiveConstruction.projectiveSpace (K := R) n)
    [IsClosedImmersion i] (F : Set X) (hF : F.Finite) :
    ∃ U : X.Opens, IsAffineOpen U ∧ F ⊆ U := by
  obtain ⟨V, hV, hFV⟩ := relative_projective_finite_set_affine_neighborhood (K := K)
    n (i '' F) (hF.image i)
  exact ⟨i ⁻¹ᵁ V, hV.preimage i, fun x hx => hFV ⟨x, hx, rfl⟩⟩

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Relative.ProjectiveAffineNeighborhoods
