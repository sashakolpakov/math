import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.CoefficientTransformations

/-! # Generating Section Frame Changes -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.GeneratingSectionFrameChanges

noncomputable section

/-! A surjective change of coefficient vectors preserves generation of a
line bundle by its section family. An invertible change also preserves the
complete-section condition. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u v w
variable {X : Scheme.{u}} {R : Type u} [CommRing R] {ι : Type v} {κ : Type w}
variable (c : R →+* Γ(X, ⊤)) (L : Line.Bundles.LineBundle X)

theorem mem_sectionNonvanishing_coefficientCombination
    (s : ι → (Line.Bundles.structureModule X ⟶ L.sheaf)) (a : ι →₀ R) (x : X)
    (hx : x ∈ Ample.LineBundles.sectionNonvanishing (Section.CoefficientTransformations.coefficientSectionCombination c L.sheaf s a)) :
    ∃ i, x ∈ Ample.LineBundles.sectionNonvanishing (s i) := by
  rw [Section.CoefficientTransformations.coefficientSectionCombination_sum] at hx
  obtain ⟨i, _, hi⟩ := L.mem_sectionNonvanishing_sum a.support _ x hx
  exact ⟨i, Scalar.SectionNonvanishing.scalarSection_nonvanishing_le L _ _ hi⟩

theorem transformSectionFamily_covers (s : ι → (Line.Bundles.structureModule X ⟶ L.sheaf))
    (hs : ∀ x : X, ∃ i, x ∈ Ample.LineBundles.sectionNonvanishing (s i))
    (T : (κ →₀ R) →ₗ[R] (ι →₀ R)) (hT : Function.Surjective T) :
    ∀ x : X, ∃ i, x ∈ Ample.LineBundles.sectionNonvanishing (Section.CoefficientTransformations.transformSectionFamily c L.sheaf s T i) := by
  intro x
  obtain ⟨i, hi⟩ := hs x
  obtain ⟨a, ha⟩ := hT (Finsupp.single i 1)
  have he : Section.CoefficientTransformations.coefficientSectionCombination c L.sheaf (Section.CoefficientTransformations.transformSectionFamily c L.sheaf s T) a = s i := by
    rw [Section.CoefficientTransformations.coefficientSectionCombination_transform, ha, Section.CoefficientTransformations.coefficientSectionCombination_single]
  apply mem_sectionNonvanishing_coefficientCombination c L _ a x
  rw [he]
  exact hi

theorem transformSectionFamily_complete (s : ι → (Line.Bundles.structureModule X ⟶ L.sheaf))
    (hs : Function.Bijective (Coefficient.SectionFrameCriterion.coefficientSectionLinearCombination c L.sheaf s))
    (T : (κ →₀ R) ≃ₗ[R] (ι →₀ R)) :
    Function.Bijective (Coefficient.SectionFrameCriterion.coefficientSectionLinearCombination c L.sheaf
      (Section.CoefficientTransformations.transformSectionFamily c L.sheaf s T.toLinearMap)) := by
  rw [Section.CoefficientTransformations.transformSectionFamily_linearCombination]
  exact hs.comp T.bijective

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.GeneratingSectionFrameChanges
