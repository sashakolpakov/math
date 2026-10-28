import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Grassmann.OverlapSchemePoints

/-! # Over Chart Points -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.OverChartPoints

noncomputable section

/-! Quotient-chart and overlap classifications for arbitrary affine schemes over the base. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable (R : Type u) [CommRing R]

/-- The coordinate algebra of an affine scheme over the base spectrum. -/
def affineOverAlgebra (T : Over (Spec (CommRingCat.of R))) [IsAffine T.left] : CommAlgCat.{u} R := by
  letI : Algebra R Γ(T.left, ⊤) :=
    (Spec.fullyFaithful.preimage (T.left.isoSpec.inv ≫ T.hom)).unop.hom.toAlgebra
  exact CommAlgCat.of R Γ(T.left, ⊤)

/-- The canonical affine presentation, as an isomorphism over the base spectrum. -/
def affineOverIso (T : Over (Spec (CommRingCat.of R))) [IsAffine T.left] :
    T ≅ (algSpec (CommRingCat.of R)).obj (Opposite.op (affineOverAlgebra R T)) := by
  refine Over.isoMk T.left.isoSpec ?_
  change T.left.isoSpec.hom ≫
    Spec.map (Spec.fullyFaithful.preimage (T.left.isoSpec.inv ≫ T.hom)).unop = T.hom
  have h := Spec.fullyFaithful.map_preimage (T.left.isoSpec.inv ≫ T.hom)
  exact (congrArg (fun f => T.left.isoSpec.hom ≫ f) h).trans
    (by simp only [Iso.hom_inv_id_assoc])

/-- Points of an affine quotient chart with an arbitrary affine source. -/
def affineOverGrassmannChartHomEquiv (k l : ℕ)
    (T : Over (Spec (CommRingCat.of R))) [IsAffine T.left] :
    (T ⟶ Grassmann.AffineCharts.grassmannAffineChart R k l) ≃
      Grassmann.Charts.GrassmannChart (affineOverAlgebra R T) (Fin l → affineOverAlgebra R T) k :=
  (affineOverIso R T).homCongr (Iso.refl _) |>.trans
    (Grassmann.AffineCharts.grassmannAffineChartHomEquiv R k l (affineOverAlgebra R T))

/-- Points of a principal overlap with an arbitrary affine source. -/
def affineOverGrassmannOverlapHomEquiv {k l : ℕ} (τ : Equiv.Perm (Fin k ⊕ Fin l))
    (T : Over (Spec (CommRingCat.of R))) [IsAffine T.left] :
    (T ⟶ Grassmann.OverlapSchemes.grassmannOverlapScheme R τ) ≃ LocalizationChartParameters.GrassmannOverlapPoint τ (affineOverAlgebra R T) :=
  (affineOverIso R T).homCongr (Iso.refl _) |>.trans
    (Grassmann.OverlapSchemes.grassmannOverlapSchemeHomEquiv R τ (affineOverAlgebra R T))

/-- The overlap inclusion forgets the alternate-frame condition for any affine source. -/
theorem affineOverGrassmannOverlapι_points {k l : ℕ} (τ : Equiv.Perm (Fin k ⊕ Fin l))
    {T : Over (Spec (CommRingCat.of R))} [IsAffine T.left] (f : T ⟶ Grassmann.OverlapSchemes.grassmannOverlapScheme R τ) :
    affineOverGrassmannChartHomEquiv R k l T (f ≫ Grassmann.OverlapSchemes.grassmannOverlapι R τ) =
      (affineOverGrassmannOverlapHomEquiv R τ T f).val := by
  simpa only [affineOverGrassmannChartHomEquiv, affineOverGrassmannOverlapHomEquiv,
    Equiv.trans_apply, Iso.homCongr_apply, Iso.refl_hom, Category.comp_id, Category.assoc] using
    Grassmann.OverlapSchemePoints.grassmannOverlapι_points R τ ((affineOverIso R T).inv ≫ f)

/-- The overlap isomorphism changes frames for any affine source. -/
theorem affineOverGrassmannOverlapIso_points {k l : ℕ} (τ : Equiv.Perm (Fin k ⊕ Fin l))
    {T : Over (Spec (CommRingCat.of R))} [IsAffine T.left] (f : T ⟶ Grassmann.OverlapSchemes.grassmannOverlapScheme R τ) :
    affineOverGrassmannOverlapHomEquiv R τ.symm T (f ≫ (Grassmann.OverlapIsomorphisms.grassmannOverlapSchemeIso R τ).hom) =
      Grassmann.OverlapEquivalence.grassmannOverlapPointEquiv τ (affineOverGrassmannOverlapHomEquiv R τ T f) := by
  simpa only [affineOverGrassmannOverlapHomEquiv, Equiv.trans_apply, Iso.homCongr_apply,
    Iso.refl_hom, Category.comp_id, Category.assoc] using
    Grassmann.OverlapSchemePoints.grassmannOverlapSchemeIso_points R τ ((affineOverIso R T).inv ≫ f)

/-- The alternate inclusion is the coordinate transition followed by forgetting the overlap. -/
theorem affineOverGrassmannAlternateι_points {k l : ℕ} (τ : Equiv.Perm (Fin k ⊕ Fin l))
    {T : Over (Spec (CommRingCat.of R))} [IsAffine T.left] (f : T ⟶ Grassmann.OverlapSchemes.grassmannOverlapScheme R τ) :
    affineOverGrassmannChartHomEquiv R k l T (f ≫ Grassmann.OverlapIsomorphisms.grassmannOverlapAlternateι R τ) =
      (Grassmann.OverlapEquivalence.grassmannOverlapPointEquiv τ (affineOverGrassmannOverlapHomEquiv R τ T f)).val := by
  calc
    _ = (affineOverGrassmannOverlapHomEquiv R τ.symm T
        (f ≫ (Grassmann.OverlapIsomorphisms.grassmannOverlapSchemeIso R τ).hom)).val := by
      simpa only [Grassmann.OverlapIsomorphisms.grassmannOverlapAlternateι, Category.assoc] using
        affineOverGrassmannOverlapι_points R τ.symm (f ≫ (Grassmann.OverlapIsomorphisms.grassmannOverlapSchemeIso R τ).hom)
    _ = _ := congrArg (fun c : LocalizationChartParameters.GrassmannOverlapPoint τ.symm (affineOverAlgebra R T) => c.val)
      (affineOverGrassmannOverlapIso_points R τ f)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.OverChartPoints
