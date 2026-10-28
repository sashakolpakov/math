import OAI.AlgebraicGeometry.Resolution.Blowups.PolynomialProjectiveBaseChange
import Mathlib.AlgebraicGeometry.AlgClosed.Basic

/-! # Projective Proportional Maps -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.ProjectiveProportionalMaps.Construction

noncomputable section

/-! Projective maps are unchanged by common unit rescalings of homogeneous coordinates. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {A B σ τ : Type u} [CommRing A] [CommRing B]
variable [SetLike σ A] [AddSubgroupClass σ A] [SetLike τ B] [AddSubgroupClass τ B]
variable {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]
variable (f g : 𝒜 →+*ᵍ ℬ)
variable (hf : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map f)
variable (hg : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map g)

/-- Common homogeneous unit factors give exactly the same projective points. -/
theorem projMap_apply_eq_of_homogeneous_units (c : ℕ → B) (hc : ∀ d, IsUnit (c d))
    (hfg : ∀ (d : ℕ) (a : A), a ∈ 𝒜 d → f a = c d * g a)
    (x : Proj ℬ) : Proj.map f hf x = Proj.map g hg x := by
  apply ProjectiveSpectrum.ext
  apply HomogeneousIdeal.ext'
  intro d a ha
  change f a ∈ x.asHomogeneousIdeal.toIdeal ↔ g a ∈ x.asHomogeneousIdeal.toIdeal
  rw [hfg d a ha]
  exact Ideal.unit_mul_mem_iff_mem _ (hc d)

/-- For a reduced scheme locally of finite type over an algebraically
closed field, these pointwise projective equalities identify the actual morphisms. -/
theorem projMap_eq_of_homogeneous_units
    {K : Type u} [Field K] [IsAlgClosed K] [IsReduced (Proj ℬ)]
    (p : Proj 𝒜 ⟶ Spec (.of K)) [LocallyOfFiniteType p] [IsSeparated p]
    [LocallyOfFiniteType (Proj.map f hf ≫ p)]
    (hover : Proj.map f hf ≫ p = Proj.map g hg ≫ p)
    (c : ℕ → B) (hc : ∀ d, IsUnit (c d))
    (hfg : ∀ (d : ℕ) (a : A), a ∈ 𝒜 d → f a = c d * g a) :
    Proj.map f hf = Proj.map g hg := by
  apply ext_of_apply_eq p Set.univ isOpen_univ.isLocallyClosed dense_univ
  · intro x _ _
    exact projMap_apply_eq_of_homogeneous_units f g hf hg c hc hfg x
  · exact hover

end

end OAI.AlgebraicGeometry.Resolution.Blowups.ProjectiveProportionalMaps.Construction
