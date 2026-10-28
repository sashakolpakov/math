import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PrescribedClosedFamilyRecovery
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Smooth.CoefficientFamilyRecovery
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Smooth.ProjectiveCoefficientModel
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Homogeneous.FamilyProjectivity
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coefficient.FamilyEmbeddingRecovery

/-! # Projective Family Descent -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Smooth closed families in a fixed projective space descend over arbitrary rings, preserving their actual ideal-defined base change. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem Closed.Families.FlatClosedFamily.exists_smooth_noetherian_projective_family
    {R : Type u} [CommRing R] {n : ℕ}
    (F : Closed.Families.FlatClosedFamily (Projective.ProjectivePresentations.affineProjectiveSpace R n)) [Smooth F.scheme.hom] :
    ∃ K : Subalgebra ℤ R, Algebra.FiniteType ℤ K ∧ IsNoetherianRing K ∧
      ∃ G : Closed.Families.FlatClosedFamily (Projective.ProjectivePresentations.affineProjectiveSpace K n), Smooth G.scheme.hom ∧
        F = G.pullbackAlong (Projective.CoefficientFunctoriality.polynomialProjectiveMap (CommRingCat.ofHom K.val.toRingHom) n)
          (Spec.map (CommRingCat.ofHom K.val.toRingHom))
          (Projective.CoefficientFunctoriality.polynomialProjectiveMap_isPullback (CommRingCat.ofHom K.val.toRingHom) n) := by
  let E := F.equations
  let C := E.coefficientRing ℤ
  let X := Projective.EmbeddingBaseChange.homogeneousProjectiveFamily (E.modelIdeal ℤ)
  let P := Homogeneous.FamilyProjectivity.homogeneousProjectiveFamilyPresentation (E.modelIdeal ℤ)
  have : Algebra.FiniteType ℤ C := inferInstanceAs (Algebra.FiniteType ℤ (E.coefficientRing ℤ))
  have : IsProper X.hom := E.coefficientModel_proper ℤ
  have : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  have : Smooth ((Over.pullback (Spec.map (CommRingCat.ofHom C.val.toRingHom))).obj X).hom :=
    E.coefficientFamily_recovery_smooth
  obtain ⟨K, hCK, hK, hKN, ⟨L⟩⟩ := HilbertConstruction.Smooth.ProjectiveCoefficientModel.exists_smooth_projective_coefficient_model C X P
  let φ : CommRingCat.of C ⟶ CommRingCat.of K := CommRingCat.ofHom (Subalgebra.inclusion hCK).toRingHom
  let ψ : CommRingCat.of K ⟶ CommRingCat.of R := CommRingCat.ofHom K.val.toRingHom
  let θ : CommRingCat.of C ⟶ CommRingCat.of R := CommRingCat.ofHom C.val.toRingHom
  have hφψ : φ ≫ ψ = θ := by rfl
  have hbase : Spec.map ψ ≫ Spec.map φ = Spec.map θ := by
    rw [← Spec.map_comp, hφψ]
  let i : X ⟶ Projective.ProjectivePresentations.affineProjectiveSpace C n := Projective.EmbeddingBaseChange.homogeneousProjectiveEmbedding (E.modelIdeal ℤ)
  have : IsClosedImmersion i.left := inferInstanceAs (IsClosedImmersion (HilbertScheme.Presentations.Projective.Quotient.GradedHilbert.projectiveQuotientInclusion (E.modelIdeal ℤ)))
  let q : F.scheme.left ⟶ X.left := E.coefficientModelMap ℤ
  have hq : IsPullback q F.scheme.hom X.hom (Spec.map ψ ≫ Spec.map φ) := by
    rw [hbase]
    exact E.coefficientModel_isPullback ℤ
  have hi : q ≫ i.left = F.inclusion.left ≫ Projective.CoefficientFunctoriality.polynomialProjectiveMap (φ ≫ ψ) n := by
    rw [hφψ]
    exact E.coefficientModelMap_embedding ℤ
  let G := L.prescribedClosedFamily φ (Spec.map ψ) i
  exact ⟨K, hK, hKN, G, L.prescribedClosedFamily_smooth φ (Spec.map ψ) i,
    L.prescribedClosedFamily_recovery φ ψ F i q hq hi⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
