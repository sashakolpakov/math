import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.NormalSupportRelative

/-! # Retraction Support -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.RetractionSupport.Constructions

noncomputable section

/-! A genuine retraction splits pullback on the original relative
groups, with the exact image of an arbitrary closed source support. -/

open _root_.CategoryTheory

open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.NormalSupportRelative.Constructions

set_option backward.isDefEq.respectTransparency false

variable {X Y : TopCat.{0}} (i : X ⟶ Y) (r : Y ⟶ X) (hr : i ≫ r = 𝟙 X) (O : Set X)

include hr

theorem source_preimage : i ⁻¹' (r ⁻¹' O) = O := by
  change (i ≫ r) ⁻¹' O = O
  rw [hr]
  rfl

theorem image_complement : (Set.range i)ᶜ ∪ r ⁻¹' O = (i '' Oᶜ)ᶜ := by
  ext y
  constructor
  · rintro (hy | hy) ⟨x, hx, hxy⟩
    · exact hy ⟨x, hxy⟩
    · have he : r (i x) = x := ConcreteCategory.congr_hom hr x
      change r y ∈ O at hy
      rw [← hxy, he] at hy
      exact hx hy
  · intro hy
    by_cases hiy : y ∈ Set.range i
    · obtain ⟨x, rfl⟩ := hiy
      right
      have he : r (i x) = x := ConcreteCategory.congr_hom hr x
      change r (i x) ∈ O
      rw [he]
      by_contra hx
      exact hy ⟨x, hx, rfl⟩
    · exact Or.inl hiy

theorem inclusion_mapsTo : Set.MapsTo i O (r ⁻¹' O) := by
  intro x hx
  change r (i x) ∈ O
  rw [show r (i x) = x from ConcreteCategory.congr_hom hr x]
  exact hx

theorem relativePullback_split (q : ℕ) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) r
      (A := r ⁻¹' O) (B := O) (fun _ hx => hx) q ≫
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) i
      (inclusion_mapsTo i r hr O) q = 𝟙 _ := by
  change HomologicalComplex.homologyMap _ q ≫ HomologicalComplex.homologyMap _ q = 𝟙 _
  rw [← HomologicalComplex.homologyMap_comp,
    AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCochainsMap_comp_eq_id (ModuleCat.of ℚ ℚ) i r
      (inclusion_mapsTo i r hr O) (fun _ hx => hx) hr, HomologicalComplex.homologyMap_id]

theorem relativePullback_split_raw (q : ℕ) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) r
      (A := r ⁻¹' O) (B := O) (fun _ hx => hx) q ≫
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) i
      (A := i ⁻¹' (r ⁻¹' O)) (B := r ⁻¹' O) (fun _ hx => hx) q ≫
    eqToHom (congrArg (fun S => AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X S q)
      (source_preimage i r hr O)) = 𝟙 _ := by
  have he := HodgeConjecture.DegreeTwo.NormalSupportRelative.Constructions.relativePairMap_supportEquality i (source_preimage i r hr O)
    (rfl : r ⁻¹' O = _) (fun _ hx => hx) (inclusion_mapsTo i r hr O) q
  simp only [eqToIso_refl, Iso.refl_hom, Category.id_comp] at he
  exact (congrArg (fun k => AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) r
    (A := r ⁻¹' O) (B := O) (fun _ hx => hx) q ≫ k) he).trans
      (relativePullback_split i r hr O q)

end

end OAI.AlgebraicGeometry.CycleClass.Thom.RetractionSupport.Constructions
