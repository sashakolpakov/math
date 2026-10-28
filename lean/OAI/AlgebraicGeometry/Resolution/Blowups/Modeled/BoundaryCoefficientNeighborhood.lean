import OAI.AlgebraicGeometry.Resolution.Blowups.Boundary.CoefficientOpenChart

/-! # Boundary Coefficient Neighborhood -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Modeled.BoundaryCoefficientNeighborhood.Construction

noncomputable section

/-! Construct the complete pointed boundary-compatible coefficient neighborhood. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u v

theorem exists_modeled_boundary_coefficient_open_chart
    {k : Type u} [Field k] (R : CommRingCat.{u}) [Algebra k R]
    {ι : Type v} [Fintype ι] (w : ι → R) (M : Blowups.Etale.BoundaryModel.Construction.EtaleBoundaryModel k R ι w)
    (J : Ideal R) (n : ℕ) (p : PrimeSpectrum R)
    (hJ : J.map (algebraMap R (Localization.AtPrime p.asIdeal)) ≤
      IsLocalRing.maximalIdeal (Localization.AtPrime p.asIdeal) ^ (n + 1))
    (hbound : Relative.LogarithmicIdeal.Construction.iteratedRelativeLogarithmicDifferentialIdeal k w J (n + 1) = ⊤) :
    Nonempty (Boundary.CoefficientOpenChart.Construction.BoundaryCoefficientOpenChart k R w J n p) := by
  classical
  let : Algebra.Smooth k R := M.smooth
  obtain ⟨C, z, E, f, hz, hzq, _, hE, ⟨N⟩, ⟨B⟩, η, hη⟩ :=
    ActiveModeledBoundaryFiber.Construction.exists_active_modeled_boundary_fiber R w M J n p hJ hbound
  let A := Localization.Away C.denominator
  let U := Localization.Away f
  let gA : A →ₐ[k] U := IsScalarTower.toAlgHom k A U
  let g : R →ₐ[k] U := IsScalarTower.toAlgHom k R U
  let : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap A U))) :=
    RefinedNormalOpen.Construction.refinedNormalOpen_isOpenImmersion E z f
  have ho : IsOpenImmersion (Spec.map (CommRingCat.ofHom g.toRingHom)) := by
    have he : CommRingCat.ofHom g.toRingHom =
        CommRingCat.ofHom (algebraMap R A) ≫ CommRingCat.ofHom (algebraMap A U) :=
      congrArg CommRingCat.ofHom (IsScalarTower.algebraMap_eq R A U)
    rw [he, Spec.map_comp]
    infer_instance
  have hgA : gA.toRingHom.Etale := (HasRingHomProperty.Spec_iff (P := @Etale)).mp
    (inferInstance : Etale (Spec.map (CommRingCat.ofHom (algebraMap A U))))
  let : Algebra.Smooth k A := Algebra.Smooth.comp k R A
  have hJmap : (J.map (algebraMap R A)).map gA.toRingHom = J.map g.toRingHom := by
    change (J.map (algebraMap R A)).map (algebraMap A U) = J.map (algebraMap R U)
    rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq R A U]
  have hz' : algebraMap A U z ∈ Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k (J.map g.toRingHom) n := by
    have h := Ideal.mem_map_of_mem gA.toRingHom hz
    rw [Blowups.Smooth.DifferentialMap.Construction.smooth_iteratedRelativeDifferentialIdeal_map k gA hgA (J.map (algebraMap R A)) n, hJmap] at h
    exact h
  obtain ⟨Q, hQ⟩ := RefinedNormalOpen.Construction.refinedNormalOpen_lifts_prime E z f C.point η hη
  have hQI : Q.asIdeal.comap (algebraMap A U) = C.point.asIdeal :=
    congrArg PrimeSpectrum.asIdeal hQ
  have hpI : C.point.asIdeal.comap (algebraMap R A) = p.asIdeal :=
    congrArg PrimeSpectrum.asIdeal C.point_over
  have hQp : PrimeSpectrum.comap g.toRingHom Q = p := by
    apply PrimeSpectrum.ext
    change Q.asIdeal.comap (algebraMap R U) = p.asIdeal
    rw [IsScalarTower.algebraMap_eq R A U, ← Ideal.comap_comap, hQI, hpI]
  have hzQ : algebraMap A U z ∈ Q.asIdeal := by
    change z ∈ Q.asIdeal.comap (algebraMap A U)
    rw [hQI]
    exact hzq
  have hEfull : E ∈ Relative.LogarithmicIdeal.Construction.relativeLogarithmicDerivations k (fun j => algebraMap R A (w j)) := by
    intro j
    by_cases hj : j ∈ C.active
    · exact hE ⟨j, hj⟩
    · rw [Ideal.span_singleton_eq_top.mpr (C.inactive_units j hj)]
      trivial
  have hD := RefinedNormalDerivative.Construction.refinedNormalDerivation_relative_logarithmic
    (fun j => algebraMap R A (w j)) E hEfull z f
  have hew : (fun j => algebraMap A U (algebraMap R A (w j))) = (fun j => g (w j)) := by
    funext j
    exact (IsScalarTower.algebraMap_apply R A U (w j)).symm
  rw [hew] at hD
  exact ⟨{ carrier := .of U
           algebra := inferInstance
           map := g
           isOpenImmersion := ho
           point := Q
           point_over := hQp
           normal := algebraMap A U z
           normal_mem := hz'
           normal_mem_point := hzQ
           derivative := RefinedNormalDerivative.Construction.refinedNormalDerivation E z f
           derivative_normal := RefinedNormalDerivative.Construction.refinedNormalDerivation_equation E z f
           derivative_tangent := hD
           ambientModel := N
           coefficientModel := B }⟩

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Modeled.BoundaryCoefficientNeighborhood.Construction
