import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.SectionHyperplanePreimage
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.FiniteMorphism

/-! # Ample Finite Section Neighborhood -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.AmpleFiniteSectionNeighborhood.Construction

noncomputable section

/-! An ample line bundle over an infinite field has a positive-power
section whose affine nonvanishing locus contains any prescribed finite
set. Both the section and its affine open are constructed. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u
variable {X S : Scheme.{u}}

theorem ample_finite_section_neighborhood_of_constants (f : X ⟶ S)
    (hS : IsField Γ(S, ⊤)) [Infinite Γ(S, ⊤)]
    (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X) (hL : L.IsAmple) (F : Set X) (hF : F.Finite) :
    ∃ (d : ℕ) (_ : 0 < d) (z : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶ (L.tensorPower d).sheaf),
      (∀ x ∈ F, x ∈ AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing z) ∧ IsAffineOpen (AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing z) := by
  let : Field Γ(S, ⊤) := hS.toField
  obtain ⟨d, hd, n, s, hs, ha⟩ := hL.projective_section_family
  let a := AbelianModuli.HilbertConstruction.SectionsProjectiveMorphism.sectionAbsoluteMorphism f s hs
  have hAffine : IsAffineHom a := AbelianModuli.HilbertConstruction.Affine.SectionMorphism.sectionAbsoluteMorphism_affine f s hs ha
  obtain ⟨c, hc⟩ := LinearHyperplaneAvoidance.Construction.exists_linear_hyperplane_avoiding n (a '' F) (hF.image a)
  let z := LinearSectionCombinations.Construction.sectionCombination s (fun i => f.appTop (c i))
  have hD := SectionHyperplanePreimage.Construction.sectionAbsoluteMorphism_preimage_linear f s hs c
  refine ⟨d, hd, z, ?_, ?_⟩
  · intro x hx
    exact (congrArg (fun U : X.Opens => x ∈ U) hD).mp (hc (a x) ⟨x, hx, rfl⟩)
  · have hU := Proj.isAffineOpen_basicOpen (AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.coordinateGrading Γ(S, ⊤) n)
      (LinearHyperplaneAvoidance.Construction.sectionLinearPolynomial c) (LinearHyperplaneAvoidance.Construction.sectionLinearPolynomial_homogeneous c) Nat.zero_lt_one
    exact (congrArg IsAffineOpen hD).mp
      (@IsAffineHom.isAffine_preimage _ _ a hAffine _ hU)

theorem ample_finite_section_neighborhood {K : Type u} [Field K] [Infinite K]
    (f : X ⟶ Spec (.of K)) (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X) (hL : L.IsAmple)
    (F : Set X) (hF : F.Finite) :
    ∃ (d : ℕ) (_ : 0 < d) (z : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶ (L.tensorPower d).sheaf),
      (∀ x ∈ F, x ∈ AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing z) ∧ IsAffineOpen (AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing z) := by
  let e := (Scheme.ΓSpecIso (.of K)).commRingCatIsoToRingEquiv
  have : Infinite Γ(Spec (.of K), ⊤) := Infinite.of_injective e.symm e.symm.injective
  exact ample_finite_section_neighborhood_of_constants f
    (e.toMulEquiv.isField (Field.toIsField K)) L hL F hF

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.AmpleFiniteSectionNeighborhood.Construction
