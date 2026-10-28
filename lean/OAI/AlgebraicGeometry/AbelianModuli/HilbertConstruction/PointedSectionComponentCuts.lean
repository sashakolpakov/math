import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.SectionPointSeparation
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ComponentwiseClosedDimensionDrop
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite

/-! # Pointed Section Component Cuts -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PointedSectionComponentCuts

noncomputable section

/-! A section through a rational point can cut every non-singleton
irreducible component of a Noetherian scheme mapping quasi-finitely to
the section's ambient scheme. Discreteness of the point fiber supplies
the points that the section must avoid. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
universe u
variable {K : Type u} [Field K] [Infinite K] {X Y : Scheme.{u}}

theorem exists_pointed_section_cutting_components [NoetherianSpace Y]
    (p : X ⟶ Spec (.of K)) (L : Line.Bundles.LineBundle X) {n : ℕ}
    (s : Fin (n + 1) → (Line.Bundles.structureModule X ⟶ L.sheaf))
    (hcover : ∀ x : X, ∃ i, x ∈ Ample.LineBundles.sectionNonvanishing (s i))
    (ha : ∀ i, IsAffineOpen (Ample.LineBundles.sectionNonvanishing (s i)))
    (hgen : Section.ProjectivePresentation.SectionRatiosGenerate p s)
    (z : Spec (.of K) ⟶ X) (hz : z ≫ p = 𝟙 _)
    (f : Y ⟶ X) [LocallyQuasiFinite f] :
    ∃ t : Line.Bundles.structureModule X ⟶ L.sheaf,
      z (IsLocalRing.closedPoint K) ∉ Ample.LineBundles.sectionNonvanishing t ∧
      ∀ C ∈ irreducibleComponents Y,
        (∀ y ∈ C, f y ∉ Ample.LineBundles.sectionNonvanishing t) → C.Subsingleton := by
  classical
  let : Finite (irreducibleComponents Y) :=
    Set.finite_coe_iff.mpr NoetherianSpace.finite_irreducibleComponents
  let J := {C : irreducibleComponents Y // ¬ C.val.Subsingleton}
  have hpoint (C : J) : ∃ y ∈ C.val.val, f y ≠ z (IsLocalRing.closedPoint K) := by
    by_contra h
    have hsub : C.val.val ⊆ f ⁻¹' {z (IsLocalRing.closedPoint K)} := by
      intro y hy
      change f y = z (IsLocalRing.closedPoint K)
      by_contra hne
      exact h ⟨y, hy, hne⟩
    exact C.property (((f.isDiscrete_preimage_singleton _).mono hsub).subsingleton_of_isPreirreducible
      C.val.property.1.2)
  choose y hy hne using hpoint
  obtain ⟨t, htz, hty⟩ := Projective.SectionPointSeparation.exists_section_vanishing_at_rationalPoint_avoiding_finite_points
    p L s hcover ha hgen z hz (fun C => f (y C)) hne
  refine ⟨t, htz, ?_⟩
  intro C hC hcontained
  by_contra hnontrivial
  let D : J := ⟨⟨C, hC⟩, hnontrivial⟩
  exact hcontained (y D) (hy D) (hty D)

theorem exists_pointed_section_dropping_dimension [NoetherianSpace Y]
    (p : X ⟶ Spec (.of K)) (L : Line.Bundles.LineBundle X) {n : ℕ}
    (s : Fin (n + 1) → (Line.Bundles.structureModule X ⟶ L.sheaf))
    (hcover : ∀ x : X, ∃ i, x ∈ Ample.LineBundles.sectionNonvanishing (s i))
    (ha : ∀ i, IsAffineOpen (Ample.LineBundles.sectionNonvanishing (s i)))
    (hgen : Section.ProjectivePresentation.SectionRatiosGenerate p s)
    (z : Spec (.of K) ⟶ X) (hz : z ≫ p = 𝟙 _)
    (f : Y ⟶ X) [LocallyQuasiFinite f]
    (d : ℕ) (hdim : topologicalKrullDim Y ≤ (d + 1 : ℕ)) :
    ∃ t : Line.Bundles.structureModule X ⟶ L.sheaf,
      z (IsLocalRing.closedPoint K) ∉ Ample.LineBundles.sectionNonvanishing t ∧
      topologicalKrullDim {y : Y | f y ∉ Ample.LineBundles.sectionNonvanishing t} ≤ d := by
  obtain ⟨t, htz, ht⟩ := exists_pointed_section_cutting_components p L s hcover ha hgen z hz f
  refine ⟨t, htz, ?_⟩
  apply ComponentwiseClosedDimensionDrop.closedCut_topologicalKrullDim_le _
    (((Ample.LineBundles.sectionNonvanishing t).isOpen.preimage f.continuous).isClosed_compl) d hdim
  intro C hC hcontained
  exact ht C hC hcontained

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PointedSectionComponentCuts
