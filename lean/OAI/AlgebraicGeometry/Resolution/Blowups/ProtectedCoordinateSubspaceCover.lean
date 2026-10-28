import OAI.AlgebraicGeometry.Resolution.Blowups.Finite.CoordinateSubspaceCover
import OAI.AlgebraicGeometry.Resolution.Blowups.Coordinate.SubspaceChartBaseExtension

/-! # Protected Coordinate Subspace Cover -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.ProtectedCoordinateSubspaceCover.Construction

noncomputable section

/-! A protected smooth part of an integral closed carrier has a finite coordinate-model cover over the original ambient scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem exists_finite_protected_coordinate_subspace_cover
    {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X]
    (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [Smooth f] (J : X.IdealSheafData) (hJ : J ≠ ⊥)
    (U : X.Opens) [Nonempty U] [CompactSpace U]
    [Smooth ((J.comap U.ι).subschemeι ≫ (U.ι ≫ f))] :
    ∃ (ι : Type) (_ : Fintype ι) (x : ι → X) (C : ∀ i, Global.CoordinateSubspaceChart.Construction.GlobalCoordinateSubspaceChart f J (x i)),
      (∀ i, x i ∈ J.support) ∧ (∀ i p, (C i).map p ∈ U) ∧
      ∀ y ∈ J.support, y ∈ U → ∃ i p, (C i).map p = y := by
  let : IsIntegral U := isIntegral_of_isOpenImmersion U.ι
  let : IsLocallyNoetherian U := LocallyOfFiniteType.isLocallyNoetherian U.ι
  have hJU : J.comap U.ι ≠ ⊥ := Global.ResidualNeighborhoodBoundary.Construction.idealSheaf_comap_nonempty_open_ne_bot U.ι J hJ
  obtain ⟨s, C, hcover⟩ := Finite.CoordinateSubspaceCover.Construction.exists_finite_global_coordinate_subspace_cover (U.ι ≫ f) (J.comap U.ι) hJU
  refine ⟨s, inferInstance, fun i => U.ι i.val.val, fun i => (C i).extendBase U.ι, ?_, ?_, ?_⟩
  · intro i
    have he := congrArg (fun T : TopologicalSpace.Closeds U => (i.val.val : U) ∈ T)
      (Scheme.IdealSheafData.support_comap J U.ι)
    exact he.mp i.val.property
  · intro i p
    exact ((C i).map p).property
  intro y hy hyU
  have hy' : (⟨y, hyU⟩ : U) ∈ (J.comap U.ι).support := by
    rw [Scheme.IdealSheafData.support_comap]
    exact hy
  obtain ⟨i, p, hp⟩ := hcover ⟨y, hyU⟩ hy'
  refine ⟨i, p, ?_⟩
  change U.ι ((C i).map p) = y
  rw [hp]
  rfl

end

end OAI.AlgebraicGeometry.Resolution.Blowups.ProtectedCoordinateSubspaceCover.Construction
