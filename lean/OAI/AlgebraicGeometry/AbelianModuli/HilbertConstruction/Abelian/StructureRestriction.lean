import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polarized.StructureOpen
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.BaseChangeCoherence

/-! # Structure Restriction -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian

noncomputable section

/-! Restricting the original family to its structure-sheaf H1 open gives
the same dimension bound on every further field-valued pullback. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u

variable {S : Scheme.{u}} [IsAffine S] [IsLocallyNoetherian S] {g : ℕ}
    (A : Schemes.AbelianScheme g S) (P : Projective.ProjectivePresentations.ProjectivePresentation A.scheme) (d : ℕ)

theorem Schemes.AbelianScheme.structureH1Bound_of_range_subset
    {T : Scheme.{u}} (c : T ⟶ S)
    (hc : Set.range c ⊆ (A.structureH1Open P d : Set S))
    {K : Type u} [Field K] (b : Spec (.of K) ⟶ T) :
    ((A.pullback c).pullback b).structureH1Dimension ≤ d := by
  have hcomp : Set.range (b ≫ c) ⊆ (A.structureH1Open P d : Set S) := by
    rintro _ ⟨k, rfl⟩
    exact hc ⟨b k, rfl⟩
  have hdim := (A.structureH1Open_field_point P d (b ≫ c)).mp hcomp
  have he := (A.pullback (b ≫ c)).structureH1Dimension_eq_of_iso
    ((A.pullback c).pullback b) (A.pullbackCompIso c b)
  exact he.symm.le.trans hdim

theorem Schemes.AbelianScheme.structureH1Open_bound
    {K : Type u} [Field K] (b : Spec (.of K) ⟶ A.structureH1Open P d) :
    ((A.pullback (A.structureH1Open P d).ι).pullback b).structureH1Dimension ≤ d :=
  A.structureH1Bound_of_range_subset P d (A.structureH1Open P d).ι
    (by simp only [Scheme.Opens.range_ι, Set.Subset.refl]) b

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian
