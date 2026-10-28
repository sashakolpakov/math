import OAI.AlgebraicGeometry.Divisors.LineBundles.Projective.CoordinateSectionMap
import OAI.AlgebraicGeometry.Divisors.LineBundles.Affine.RegularRestriction

/-! # Linear Chart Basis -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Projective.LinearChartBasis.BundleCycles

noncomputable section

/-! Affine subopens of linear projective charts give a genuine
basis, with compatible restricted homogeneous coordinate fractions. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace

variable {A σ : Type} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    (𝒜 : ℕ → σ) [GradedRing 𝒜]

def projectiveLinearChartBasis : Set (Proj 𝒜).Opens :=
  {U | IsAffineOpen U ∧ ∃ v : A, v ∈ 𝒜 1 ∧ U ≤ Proj.basicOpen 𝒜 v}

theorem projectiveLinearChartBasis_isBasis
    (hcover : ∀ x : Proj 𝒜, ∃ v : A, v ∈ 𝒜 1 ∧ x ∈ Proj.basicOpen 𝒜 v) :
    Opens.IsBasis (projectiveLinearChartBasis 𝒜) := by
  apply Opens.isBasis_iff_nbhd.mpr
  intro U x hx
  obtain ⟨v, hv, hxv⟩ := hcover x
  obtain ⟨V, hV, hxV, hVU⟩ := exists_isAffineOpen_mem_and_subset (show x ∈ U ⊓ Proj.basicOpen 𝒜 v from ⟨hx, hxv⟩)
  exact ⟨V, ⟨hV, v, hv, hVU.trans inf_le_right⟩, hxV, hVU.trans inf_le_left⟩

def projectiveLinearChartDenominator (U : projectiveLinearChartBasis 𝒜) : A := U.2.2.choose

theorem projectiveLinearChartDenominator_degree (U : projectiveLinearChartBasis 𝒜) :
    projectiveLinearChartDenominator 𝒜 U ∈ 𝒜 1 := U.2.2.choose_spec.1

theorem projectiveLinearChartDenominator_bound (U : projectiveLinearChartBasis 𝒜) :
    U.1 ≤ Proj.basicOpen 𝒜 (projectiveLinearChartDenominator 𝒜 U) := U.2.2.choose_spec.2

def projectiveLinearChartSection (t : A) (ht : t ∈ 𝒜 1) (U : projectiveLinearChartBasis 𝒜) : Γ(Proj 𝒜, U.1) :=
  (Proj 𝒜).presheaf.map (homOfLE (projectiveLinearChartDenominator_bound 𝒜 U)).op
    (CoordinateSectionMap.BundleCycles.projectiveCoordinateSection 𝒜 (projectiveLinearChartDenominator 𝒜 U) t
      (projectiveLinearChartDenominator_degree 𝒜 U) ht)

theorem projectiveLinearChartSection_regular (t : A) (ht : t ∈ 𝒜 1) (hreg : IsRegular t)
    (U : projectiveLinearChartBasis 𝒜) : IsRegular (projectiveLinearChartSection 𝒜 t ht U) :=
  Affine.RegularRestriction.BundleCycles.affineRestriction_regular
    ⟨Proj.basicOpen 𝒜 (projectiveLinearChartDenominator 𝒜 U),
      Proj.isAffineOpen_basicOpen 𝒜 _ (projectiveLinearChartDenominator_degree 𝒜 U) (by decide)⟩
    ⟨U.1, U.2.1⟩ (projectiveLinearChartDenominator_bound 𝒜 U) _
    (CoordinateSectionMap.BundleCycles.projectiveCoordinateSection_regular 𝒜 _ t (projectiveLinearChartDenominator_degree 𝒜 U) ht hreg)

theorem projectiveLinearChartSection_cross (t u : A) (ht : t ∈ 𝒜 1) (hu : u ∈ 𝒜 1)
    (U V : projectiveLinearChartBasis 𝒜) (h : U.1 ≤ V.1) :
    projectiveLinearChartSection 𝒜 t ht U * (Proj 𝒜).presheaf.map (homOfLE h).op (projectiveLinearChartSection 𝒜 u hu V) =
      projectiveLinearChartSection 𝒜 u hu U * (Proj 𝒜).presheaf.map (homOfLE h).op (projectiveLinearChartSection 𝒜 t ht V) := by
  have hr (a : Γ(Proj 𝒜, Proj.basicOpen 𝒜 (projectiveLinearChartDenominator 𝒜 V))) :
      (Proj 𝒜).presheaf.map (homOfLE h).op
        ((Proj 𝒜).presheaf.map (homOfLE (projectiveLinearChartDenominator_bound 𝒜 V)).op a) =
      (Proj 𝒜).presheaf.map (homOfLE (h.trans (projectiveLinearChartDenominator_bound 𝒜 V))).op a := by
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
    rfl
  unfold projectiveLinearChartSection
  rw [hr, hr]
  exact CoordinateSectionMap.BundleCycles.projectiveCoordinateSection_cross 𝒜 _ _ t u (projectiveLinearChartDenominator_degree 𝒜 U)
    (projectiveLinearChartDenominator_degree 𝒜 V) ht hu U.1
    (projectiveLinearChartDenominator_bound 𝒜 U) (h.trans (projectiveLinearChartDenominator_bound 𝒜 V))

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Projective.LinearChartBasis.BundleCycles
