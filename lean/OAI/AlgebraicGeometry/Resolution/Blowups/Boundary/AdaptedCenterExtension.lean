import OAI.AlgebraicGeometry.Resolution.Blowups.Boundary.AdaptedCenterChart

/-! # Adapted Center Extension -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Boundary.AdaptedCenterExtension.Construction

noncomputable section

/-! Add one exact boundary equation to an already adapted actual center chart. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable (k : Type u) [CommRing k]

/-- A transverse first boundary equation extends a chart retaining the
remaining equations. The new map is still an actual open immersion
through the original point and defines exactly the original center there. -/
theorem extend_boundary_adapted_center_chart
    (R : CommRingCat.{u}) [Algebra k R] (I : Ideal R) {n : ℕ}
    (w : Fin (n + 1) → R) (p : PrimeSpectrum R) (hIp : I ≤ p.asIdeal)
    (E : Derivation k R R) (hE0 : E (w 0) = 1) (hEtail : ∀ j : Fin n, E (w j.succ) = 0)
    (hw0 : w 0 ∈ I)
    (C : AdaptedCenterChart.Construction.BoundaryAdaptedCenterOpenChart k R I (fun j : Fin n => w j.succ) p) :
    Nonempty (AdaptedCenterChart.Construction.BoundaryAdaptedCenterOpenChart k R I w p) := by
  classical
  let A := C.carrier
  have het : Etale (Spec.map (CommRingCat.ofHom C.map.toRingHom)) := inferInstance
  have hf : C.map.toRingHom.Etale :=
    (HasRingHomProperty.Spec_iff (P := @Etale)).mp het
  let E' : Derivation k A A := Blowups.Etale.DerivationHom.Construction.extendEtaleRingDerivationHom k C.map.toRingHom hf C.map.commutes E
  have hE' (r : R) : E' (C.map r) = C.map (E r) :=
    Blowups.Etale.DerivationHom.Construction.extendEtaleRingDerivationHom_apply k C.map.toRingHom hf C.map.commutes E r
  have hcomap : C.point.asIdeal.comap C.map.toRingHom = p.asIdeal := congrArg PrimeSpectrum.asIdeal C.point_over
  have hIpoint : I.map C.map.toRingHom ≤ C.point.asIdeal := by
    rw [Ideal.map_le_iff_le_comap, hcomap]
    exact hIp
  have hg (j : C.indices) : C.generators j ∈ C.point.asIdeal :=
    hIpoint (C.centerSpan ▸ Ideal.subset_span ⟨j, rfl⟩)
  have hz : C.map (w 0) ∈ Ideal.span (Set.range C.generators) := by
    rw [C.centerSpan]
    exact Ideal.mem_map_of_mem C.map.toRingHom hw0
  have hEz : E' (C.map (w 0)) ∉ C.point.asIdeal := by
    rw [hE', hE0, map_one]
    exact C.point.isPrime.one_notMem
  let B : Finset C.indices := Finset.univ.image C.boundaryIndex
  have hEB (j : C.indices) (hj : j ∈ B) : E' (C.generators j) = 0 := by
    obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp hj
    rw [C.boundaryCoordinates]
    rw [hE', hEtail, map_zero]
  obtain ⟨s, hs, i, hiB, F, hcenter, hF⟩ := Pointed.BoundaryCenterReplacement.Construction.exists_pointed_boundary_center_replacement
    C.generators C.derivations C.dual (C.map (w 0)) hz E' C.point.asIdeal hg hEz B hEB
  let S := Localization.Away s
  let f₂ : A →ₐ[k] S := IsScalarTower.toAlgHom k A S
  let f : R →ₐ[k] S := f₂.comp C.map
  have hopen : IsOpenImmersion (Spec.map (CommRingCat.ofHom f.toRingHom)) := by
    let : IsOpenImmersion (Spec.map (CommRingCat.ofHom f₂.toRingHom)) := IsOpenImmersion.of_isLocalization s
    change IsOpenImmersion (Spec.map (CommRingCat.ofHom C.map.toRingHom ≫ CommRingCat.ofHom f₂.toRingHom))
    rw [Spec.map_comp]
    infer_instance
  obtain ⟨Q, hQ⟩ := Blowups.Etale.RefinementHelpers.Construction.exists_localization_away_prime s C.point hs
  have hpoint : PrimeSpectrum.comap f.toRingHom Q = p := by
    apply PrimeSpectrum.ext
    change Q.asIdeal.comap ((algebraMap A S).comp C.map.toRingHom) = p.asIdeal
    have hQI : Q.asIdeal.comap (algebraMap A S) = C.point.asIdeal := congrArg PrimeSpectrum.asIdeal hQ
    rw [← Ideal.comap_comap, hQI, hcomap]
  have hi (j : Fin n) : i ≠ C.boundaryIndex j := by
    intro he
    apply hiB
    exact Finset.mem_image.mpr ⟨j, Finset.mem_univ j, he.symm⟩
  let G := CenterGeneratorReplacement.Construction.centerReplacementFamily (fun j => algebraMap A S (C.generators j)) i
    (algebraMap A S (C.map (w 0)))
  have hspan : Ideal.span (Set.range G) = I.map f.toRingHom := by
    rw [hcenter, C.centerSpan, Ideal.map_map]
    rfl
  refine ⟨{ carrier := .of S
            algebra := inferInstance
            map := f
            isOpenImmersion := hopen
            point := Q
            point_over := hpoint
            indices := Option {j : C.indices // i ≠ j}
            finite := inferInstance
            decidableEq := inferInstance
            generators := G
            derivations := F
            dual := hF
            centerSpan := hspan
            boundaryIndex := AdaptedCenterChart.Construction.insertRetainedCenterIndex C.boundaryIndex i hi
            boundaryCoordinates := ?_ }⟩
  intro j
  refine Fin.cases ?_ (fun t => ?_) j
  · rw [AdaptedCenterChart.Construction.insertRetainedCenterIndex_zero]
    rfl
  · rw [AdaptedCenterChart.Construction.insertRetainedCenterIndex_succ]
    change algebraMap A S (C.generators (C.boundaryIndex t)) = f (w t.succ)
    rw [C.boundaryCoordinates]
    rfl

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Boundary.AdaptedCenterExtension.Construction
