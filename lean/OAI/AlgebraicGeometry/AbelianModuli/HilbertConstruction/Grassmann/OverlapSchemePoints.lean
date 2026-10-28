import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Grassmann.OverlapIsomorphisms

/-! # Overlap Scheme Points -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Grassmann.OverlapSchemePoints

noncomputable section

/-! The overlap scheme isomorphism induces the specified transition on affine test schemes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable (R : Type u) [CommRing R] {k l : ℕ} (τ : Equiv.Perm (Fin k ⊕ Fin l))

/-- The scheme and algebra classifications agree on affine morphisms. -/
theorem grassmannOverlapSchemeHomEquiv_map {A : CommAlgCat.{u} R}
    (f : OverlapSchemes.grassmannOverlapCoordinateAlgebra R τ ⟶ A) :
    OverlapSchemes.grassmannOverlapSchemeHomEquiv R τ A ((algSpec (CommRingCat.of R)).map f.op) =
      (OverlapFunctor.grassmannOverlapCorepresentable R τ).homEquiv f := by
  change (OverlapFunctor.grassmannOverlapCorepresentable R τ).homEquiv
    (((algSpec.fullyFaithful (R := CommRingCat.of R)).homEquiv.symm
      ((algSpec.fullyFaithful (R := CommRingCat.of R)).homEquiv f.op)).unop) = _
  rw [Equiv.symm_apply_apply]
  rfl

/-- The actual scheme isomorphism acts by the prescribed coordinate transition on every affine test. -/
theorem grassmannOverlapSchemeIso_points {A : CommAlgCat.{u} R}
    (f : (algSpec (CommRingCat.of R)).obj (Opposite.op A) ⟶ OverlapSchemes.grassmannOverlapScheme R τ) :
    OverlapSchemes.grassmannOverlapSchemeHomEquiv R τ.symm A (f ≫ (OverlapIsomorphisms.grassmannOverlapSchemeIso R τ).hom) =
      OverlapEquivalence.grassmannOverlapPointEquiv τ (OverlapSchemes.grassmannOverlapSchemeHomEquiv R τ A f) := by
  obtain ⟨g, rfl⟩ := (algSpec.fullyFaithful (R := CommRingCat.of R)).homEquiv.surjective f
  calc
    _ = OverlapSchemes.grassmannOverlapSchemeHomEquiv R τ.symm A
        ((algSpec (CommRingCat.of R)).map ((OverlapIsomorphisms.grassmannOverlapAlgebraIso R τ).inv ≫ g.unop).op) :=
      congrArg (OverlapSchemes.grassmannOverlapSchemeHomEquiv R τ.symm A)
        ((algSpec (CommRingCat.of R)).map_comp g (OverlapIsomorphisms.grassmannOverlapAlgebraIso R τ).inv.op).symm
    _ = OverlapEquivalence.grassmannOverlapPointEquiv τ ((OverlapFunctor.grassmannOverlapCorepresentable R τ).homEquiv g.unop) :=
      (grassmannOverlapSchemeHomEquiv_map R τ.symm _).trans (OverlapIsomorphisms.grassmannOverlapAlgebraIso_comp R τ _)
    _ = _ := congrArg (OverlapEquivalence.grassmannOverlapPointEquiv τ) (grassmannOverlapSchemeHomEquiv_map R τ g.unop).symm

/-- The affine quotient-chart classification agrees with the polynomial-algebra classification. -/
theorem grassmannAffineChartHomEquiv_map {A : CommAlgCat.{u} R}
    (f : ChartRepresentability.grassmannChartCoordinateAlgebra R k l ⟶ A) :
    AffineCharts.grassmannAffineChartHomEquiv R k l A ((algSpec (CommRingCat.of R)).map f.op) =
      (ChartRepresentability.grassmannChartCorepresentable R k l).homEquiv f := by
  change (ChartRepresentability.grassmannChartCorepresentable R k l).homEquiv
    (((algSpec.fullyFaithful (R := CommRingCat.of R)).homEquiv.symm
      ((algSpec.fullyFaithful (R := CommRingCat.of R)).homEquiv f.op)).unop) = _
  rw [Equiv.symm_apply_apply]
  rfl

/-- The overlap inclusion forgets the alternate-frame condition on affine points. -/
theorem grassmannOverlapι_points {A : CommAlgCat.{u} R}
    (f : (algSpec (CommRingCat.of R)).obj (Opposite.op A) ⟶ OverlapSchemes.grassmannOverlapScheme R τ) :
    AffineCharts.grassmannAffineChartHomEquiv R k l A (f ≫ OverlapSchemes.grassmannOverlapι R τ) =
      (OverlapSchemes.grassmannOverlapSchemeHomEquiv R τ A f).val := by
  obtain ⟨g, rfl⟩ := (algSpec.fullyFaithful (R := CommRingCat.of R)).homEquiv.surjective f
  let j : ChartRepresentability.grassmannChartCoordinateAlgebra R k l ⟶ OverlapSchemes.grassmannOverlapCoordinateAlgebra R τ :=
    CommAlgCat.ofHom (Algebra.algHom R (MvPolynomial (Fin k × Fin l) R)
      (Localization.Away (Chart.OverlapDeterminants.chartOverlapPolynomial R τ)))
  calc
    _ = AffineCharts.grassmannAffineChartHomEquiv R k l A ((algSpec (CommRingCat.of R)).map (j ≫ g.unop).op) :=
      congrArg (AffineCharts.grassmannAffineChartHomEquiv R k l A)
        ((algSpec (CommRingCat.of R)).map_comp g j.op).symm
    _ = _ := by
      have h := grassmannAffineChartHomEquiv_map R (j ≫ g.unop)
      have h' := congrArg (fun c : LocalizationChartParameters.GrassmannOverlapPoint τ A => c.val)
        (grassmannOverlapSchemeHomEquiv_map R τ g.unop)
      exact h.trans h'.symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Grassmann.OverlapSchemePoints
