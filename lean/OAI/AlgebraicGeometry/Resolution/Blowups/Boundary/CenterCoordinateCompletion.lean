import OAI.AlgebraicGeometry.Resolution.Blowups.Boundary.CoordinateCenterChart

/-! # Center Coordinate Completion -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Boundary.CenterCoordinateCompletion.Construction

noncomputable section

/-! Complete a boundary-adapted center frame to actual étale ambient coordinates. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable (k : Type u) [CommRing k]

/-- Complete the adapted center frame relative to the original ground
ring. The original center ideal and every boundary equation become exact
coordinate subsets on an actual affine open through the original point. -/
theorem complete_boundary_adapted_center_open_chart
    (R : CommRingCat.{u}) [Algebra k R] [Algebra.Smooth k R]
    (I : Ideal R) {n : ℕ} (w : Fin n → R) (p : PrimeSpectrum R)
    (C : AdaptedCenterChart.Construction.BoundaryAdaptedCenterOpenChart k R I w p) :
    Nonempty (CoordinateCenterChart.Construction.BoundaryCoordinateCenterOpenChart k R I w p) := by
  classical
  let A := C.carrier
  have het : Etale (Spec.map (CommRingCat.ofHom C.map.toRingHom)) := inferInstance
  have hf : C.map.toRingHom.Etale := (HasRingHomProperty.Spec_iff (P := @Etale)).mp het
  let : Algebra.Smooth k A := Blowups.Etale.RefinementHelpers.Construction.smooth_target_of_etale_algHom k C.map hf
  obtain ⟨t, ht, d, φ, hφ, hφk, hX⟩ := AdaptedEtaleFrame.Construction.exists_adapted_etale_frame
    C.derivations C.generators C.dual C.point.asIdeal
  let S := Localization.Away t
  let f₂ : A →ₐ[k] S := IsScalarTower.toAlgHom k A S
  let f : R →ₐ[k] S := f₂.comp C.map
  have hopen : IsOpenImmersion (Spec.map (CommRingCat.ofHom f.toRingHom)) := by
    let : IsOpenImmersion (Spec.map (CommRingCat.ofHom f₂.toRingHom)) := IsOpenImmersion.of_isLocalization t
    change IsOpenImmersion (Spec.map (CommRingCat.ofHom C.map.toRingHom ≫ CommRingCat.ofHom f₂.toRingHom))
    rw [Spec.map_comp]
    infer_instance
  obtain ⟨Q, hQ⟩ := Blowups.Etale.RefinementHelpers.Construction.exists_localization_away_prime t C.point ht
  have hpoint : PrimeSpectrum.comap f.toRingHom Q = p := by
    apply PrimeSpectrum.ext
    change Q.asIdeal.comap ((algebraMap A S).comp C.map.toRingHom) = p.asIdeal
    have hQI : Q.asIdeal.comap (algebraMap A S) = C.point.asIdeal := congrArg PrimeSpectrum.asIdeal hQ
    have hCp : C.point.asIdeal.comap C.map.toRingHom = p.asIdeal := congrArg PrimeSpectrum.asIdeal C.point_over
    rw [← Ideal.comap_comap, hQI, hCp]
  let τ := Fin d ⊕ C.indices
  let e : C.indices ↪ τ := ⟨Sum.inr, Sum.inr_injective⟩
  let B : Finset τ := Finset.univ.image e
  have hmapI : I.map f.toRingHom = Ideal.span (Set.range (fun j => algebraMap A S (C.generators j))) := by
    change I.map ((algebraMap A S).comp C.map.toRingHom) = _
    rw [← Ideal.map_map, ← C.centerSpan, Ideal.map_span, ← Set.range_comp]
    rfl
  have hcoordI : (SubsetCoordinateBlowup.Construction.subsetCoordinateIdeal B).map φ =
      Ideal.span (Set.range (fun j => algebraMap A S (C.generators j))) := by
    rw [CoordinateCenterChart.Construction.subsetCoordinateIdeal_map_embedded_family e φ]
    apply congrArg Ideal.span
    apply congrArg Set.range
    funext j
    exact hX j
  refine ⟨{ carrier := .of S
            algebra := inferInstance
            map := f
            isOpenImmersion := hopen
            point := Q
            point_over := hpoint
            indices := τ
            finite := inferInstance
            decidableEq := inferInstance
            coordinateMap := φ
            coordinateEtale := hφ
            coordinateGround := hφk
            centerIndices := B
            centerIdeal := hmapI.trans hcoordI.symm
            boundaryIndex := C.boundaryIndex.trans e
            boundary_in_center := ?_
            boundaryCoordinates := ?_ }⟩
  · intro j
    exact Finset.mem_image.mpr ⟨C.boundaryIndex j, Finset.mem_univ _, rfl⟩
  · intro j
    change φ (MvPolynomial.X (Sum.inr (C.boundaryIndex j))) = f (w j)
    rw [hX, C.boundaryCoordinates]
    rfl

/-- Any finite smooth boundary frame contained in an actual framed center
admits simultaneous center and boundary coordinates near every point of
the center, with all original equations and point maps retained. -/
theorem exists_boundary_coordinate_center_open_chart
    (R : CommRingCat.{u}) [Algebra k R] [Algebra.Smooth k R]
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    (g : ι → R) (D : ι → Derivation k R R)
    (hD : ∀ i j, D i (g j) = if i = j then 1 else 0)
    {n : ℕ} (w : Fin n → R) (E : Fin n → Derivation k R R)
    (hE : ∀ i j, E i (w j) = if i = j then 1 else 0)
    (hw : ∀ i, w i ∈ Ideal.span (Set.range g))
    (p : PrimeSpectrum R) (hgp : Ideal.span (Set.range g) ≤ p.asIdeal) :
    Nonempty (CoordinateCenterChart.Construction.BoundaryCoordinateCenterOpenChart k R (Ideal.span (Set.range g)) w p) := by
  obtain ⟨C⟩ := AdaptedCenterExistence.Construction.exists_boundary_adapted_center_open_chart k n R g D hD w E hE hw p hgp
  exact complete_boundary_adapted_center_open_chart k R _ w p C

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Boundary.CenterCoordinateCompletion.Construction
