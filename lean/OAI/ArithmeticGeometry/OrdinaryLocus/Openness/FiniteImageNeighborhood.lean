import Mathlib.AlgebraicGeometry.ZariskisMainTheorem

/-! # Finite Image Neighborhood -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.FiniteImageNeighborhood.Construction

noncomputable section

/-! Finite images of proper fibers persist over a neighborhood in the base. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem finite_image_fiber_neighborhood
    {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S) (s : S)
    (hs : (f '' ((f ≫ g) ⁻¹' {s})).Finite)
    [IsProper (f ≫ g)] [IsSeparated g] [LocallyOfFiniteType g] :
    ∃ U : S.Opens, s ∈ U ∧ ∀ x : U.toScheme, (g ⁻¹' {x.1} ∩ Set.range f).Finite := by
  have : IsProper f := .of_comp f g
  obtain ⟨U, hsU, hU⟩ :=
    exists_finite_imageι_comp_morphismRestrict_of_finite_image_preimage f g s hs
  refine ⟨U, hsU, fun x ↦ ?_⟩
  refine ((((f.imageι ≫ g) ∣_ U).finite_preimage_singleton x).image
    (Scheme.Opens.ι _ ≫ f.imageι)).subset ?_
  rintro y ⟨hy, z, rfl⟩
  have ht : (f.imageι ≫ g) (f.toImage z) = x.1 := by
    change (f.toImage ≫ f.imageι ≫ g) z = x.1
    rw [Scheme.Hom.toImage_imageι_assoc]
    exact hy
  let a : ((f.imageι ≫ g) ⁻¹ᵁ U).toScheme :=
    ⟨f.toImage z, by change (f.imageι ≫ g) (f.toImage z) ∈ U; rw [ht]; exact x.2⟩
  refine ⟨a, ?_, ?_⟩
  · change ((f.imageι ≫ g) ∣_ U) a = x
    apply Subtype.ext
    exact (congrArg (fun q : ((f.imageι ≫ g) ⁻¹ᵁ U).toScheme ⟶ S ↦ q a)
      (morphismRestrict_ι (f.imageι ≫ g) U)).trans ht
  · change (f.toImage ≫ f.imageι) z = f z
    rw [Scheme.Hom.toImage_imageι]

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.FiniteImageNeighborhood.Construction
