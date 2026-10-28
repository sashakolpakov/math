import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Affine.ChartMatrixRecovery

/-! # Point Principal Charts -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Grassmannian.PointPrincipalCharts

noncomputable section

/-! Every affine Grassmannian point has normalized matrix coordinates on principal neighborhoods. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {ι ν : Type u} [Fintype ι] [Fintype ν] [DecidableEq ι] [DecidableEq ν]
variable (R : CommRingCat.{u})

omit [Fintype ν] [DecidableEq ν] in
theorem grassmannian_point_principal_chart
    (g : Over.mk (𝟙 (Spec R)) ⟶ Gluing.grassmannianOver (ι := ι) (ν := ν) (Spec R))
    (p : PrimeSpectrum R) :
    ∃ (r : R) (a : ι → ν) (Q : Matrix ι ν (Localization.Away r)) (hQ : Normalized.Matrices.Grassmannian.IsNormalized a Q),
      r ∉ p.asIdeal ∧ (Relative.AffinePoints.relativeAffineScheme R (Localization.Away r)).hom ≫ g.left =
        (Affine.NormalizedMatrixPoints.Grassmannian.affineNormalizedClassifyingMap R (Localization.Away r) a Q hQ).left := by
  obtain ⟨a, y, hy⟩ := Gluing.grassmannianCharts_cover (Spec R) (g.left p)
  let U : (Spec R).Opens := g.left ⁻¹ᵁ (Gluing.grassmannianChartMap a (Spec R)).opensRange
  have hp : p ∈ U := ⟨y, hy⟩
  obtain ⟨V, ⟨r, rfl⟩, hpr, hV⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.isOpen_iff.mp U.isOpen p hp
  let T := Relative.AffinePoints.relativeAffineScheme R (Localization.Away r)
  have hRange : Set.range (T.hom ≫ g.left) ⊆ Set.range (Gluing.grassmannianChartMap a (Spec R)) := by
    rintro _ ⟨x, rfl⟩
    have hx : T.hom x ∈ PrimeSpectrum.basicOpen r := by
      rw [← Scheme.Hom.opensRange_localizationAway r]
      exact ⟨x, rfl⟩
    exact hV hx
  let k := IsOpenImmersion.lift (Gluing.grassmannianChartMap a (Spec R)) (T.hom ≫ g.left) hRange
  have hk : k ≫ Gluing.grassmannianChartMap a (Spec R) = T.hom ≫ g.left :=
    IsOpenImmersion.lift_fac _ _ _
  have hb : k ≫ (Normalized.Chart.Grassmannian.normalizedChart a (Spec R)).hom = T.hom := by
    calc
      _ = k ≫ Gluing.grassmannianChartMap a (Spec R) ≫ Gluing.grassmannianStructureMap (Spec R) :=
        congrArg (fun h => k ≫ h) (Gluing.grassmannianChartMap_structureMap a (Spec R)).symm
      _ = T.hom ≫ g.left ≫ Gluing.grassmannianStructureMap (Spec R) := by
        rw [← Category.assoc, hk]
        exact Category.assoc _ _ _
      _ = T.hom := (congrArg (fun h => T.hom ≫ h) g.w).trans (Category.comp_id T.hom)
  let f : T ⟶ Normalized.Chart.Grassmannian.normalizedChart a (Spec R) := Over.homMk k hb
  obtain ⟨Q, hQ, h⟩ := Affine.ChartMatrixRecovery.Grassmannian.affine_chart_matrix_recovery R (Localization.Away r) a f
  refine ⟨r, a, Q, hQ, hpr, ?_⟩
  exact hk.symm.trans (congrArg Over.Hom.left h)

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Grassmannian.PointPrincipalCharts
