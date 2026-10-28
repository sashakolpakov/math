import OAI.AlgebraicGeometry.Resolution.Blowups.Curve.BoundaryCenterLocalEquality
import OAI.AlgebraicGeometry.Resolution.Blowups.UnitBoundaryNormalCenter
import OAI.AlgebraicGeometry.Resolution.Blowups.UnitBoundaryPrincipalNeighborhood
import OAI.AlgebraicGeometry.Resolution.Blowups.LocalContainmentNeighborhood
import OAI.AlgebraicGeometry.Resolution.Blowups.BoundaryModel.Smooth

/-! # Curve Boundary Center -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups

noncomputable section

/-! Intrinsic curve centers admit common coordinates with every labelled normal-crossing boundary. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u v

theorem Etale.BoundaryModel.Construction.EtaleBoundaryModel.curve_center_chart_at_boundary
    {k : Type u} [Field k] [IsAlgClosed k] {R : CommRingCat.{u}}
    [Algebra k R] [Algebra ℚ R] {β : Type v} [Fintype β] {w : β → R}
    (M : Blowups.Etale.BoundaryModel.Construction.EtaleBoundaryModel k R β w) (hd : ringKrullDim R ≤ 1)
    (I : Ideal R) (hI : Relative.DifferentialBlowup.Construction.firstRelativeDifferentialIdeal k I = ⊤)
    (q : Ideal R) [q.IsMaximal] (hIq : I ≤ q) (j : β) (hj : w j ∈ q) :
    ∃ F : Finset β, Nonempty (MixedBoundary.CenterCharts.Construction.MixedBoundaryCoordinateCenterOpenChart k R I w F ⟨q, inferInstance⟩) := by
  classical
  let : Algebra (MvPolynomial M.indices k) R := M.map.toAlgebra
  let : IsScalarTower k (MvPolynomial M.indices k) R :=
    IsScalarTower.of_algebraMap_eq (fun c => (M.ground c).symm)
  let : Algebra.Etale (MvPolynomial M.indices k) R := RingHom.etale_algebraMap.mp M.etale
  let : Algebra.Smooth k R := M.smooth
  let : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing k R
  cases hc : M.coordinate j with
  | none =>
      have hu : IsUnit (w j) := by
        rw [M.equation j, hc, mul_one]
        exact M.multiplierUnit j
      exact False.elim ((inferInstance : q.IsMaximal).ne_top (Ideal.eq_top_of_isUnit_mem q hj hu))
  | some i =>
      have hi : M.map (MvPolynomial.X i) ∈ q := by
        apply (q.unit_mul_mem_iff_mem (M.multiplierUnit j)).mp
        simpa only [M.equation j, hc] using hj
      have hlocal : I.map (algebraMap R (Localization.AtPrime q)) =
          (Ideal.span {M.map (MvPolynomial.X i)}).map (algebraMap R (Localization.AtPrime q)) := by
        rw [Ideal.map_span, Set.image_singleton]
        exact Curve.BoundaryCenterLocalEquality.Construction.etale_curve_center_local_eq_coordinate hd I hI q hIq i hi
      obtain ⟨r, hr, he⟩ := LocalContainmentNeighborhood.Construction.exists_neighborhood_ideal_equality I (Ideal.span {M.map (MvPolynomial.X i)})
        q (IsNoetherian.noetherian I) (IsNoetherian.noetherian _) hlocal
      let S := Localization.Away r
      let φ : R →ₐ[k] S := IsScalarTower.toAlgHom k R S
      have hφ : φ.toRingHom.Etale := RingHom.etale_algebraMap.mpr (Algebra.Etale.of_isLocalizationAway r)
      let B := M.baseChange φ hφ
      let F := Finset.univ.filter (fun l => M.coordinate l = some i)
      obtain ⟨P, hP⟩ := Blowups.Etale.RefinementHelpers.Construction.exists_localization_away_prime r (⟨q, inferInstance⟩ : PrimeSpectrum R) hr
      refine ⟨F, ⟨{
        chart := {
          carrier := .of S
          algebra := inferInstance
          map := φ
          isOpenImmersion := IsOpenImmersion.of_isLocalization r
          point := P
          point_over := hP
          model := B }
        coordinates := {i}
        center_eq := ?_
        divided_iff := ?_ }⟩⟩
      · change I.map (algebraMap R S) =
          (SubsetCoordinateBlowup.Construction.subsetCoordinateIdeal ({i} : Finset M.indices)).map (φ.toRingHom.comp M.map)
        rw [he, Ideal.map_span, Set.image_singleton, SubsetCoordinateBlowup.Construction.subsetCoordinateIdeal,
          Finset.coe_singleton, Set.image_singleton, Ideal.map_span, Set.image_singleton]
        rfl
      · intro l
        change l ∈ F ↔ ∃ s ∈ ({i} : Finset M.indices), M.coordinate l = some s
        simp only [F, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton,
          exists_eq_left]

theorem Etale.BoundaryModel.Construction.EtaleBoundaryModel.curve_center_chart
    {k : Type u} [Field k] [IsAlgClosed k] {R : CommRingCat.{u}}
    [Algebra k R] [Algebra ℚ R] {β : Type v} [Fintype β] {w : β → R}
    (M : Blowups.Etale.BoundaryModel.Construction.EtaleBoundaryModel k R β w) (hd : ringKrullDim R ≤ 1)
    (I : Ideal R) (hI : Relative.DifferentialBlowup.Construction.firstRelativeDifferentialIdeal k I = ⊤)
    (q : Ideal R) [q.IsMaximal] (hIq : I ≤ q) :
    ∃ F : Finset β, Nonempty (MixedBoundary.CenterCharts.Construction.MixedBoundaryCoordinateCenterOpenChart k R I w F ⟨q, inferInstance⟩) := by
  classical
  by_cases hw : ∃ j, w j ∈ q
  · obtain ⟨j, hj⟩ := hw
    exact M.curve_center_chart_at_boundary hd I hI q hIq j hj
  · obtain ⟨r, hr, hunit⟩ := UnitBoundaryPrincipalNeighborhood.Construction.exists_unit_boundary_principal_neighborhood w
      (⟨q, inferInstance⟩ : PrimeSpectrum R) (by simpa only [not_exists] using hw)
    let S := Localization.Away r
    let φ : R →ₐ[k] S := IsScalarTower.toAlgHom k R S
    let : Algebra.Smooth k R := M.smooth
    let : Algebra.Etale R S := Algebra.Etale.of_isLocalizationAway r
    let : Algebra.Smooth k S := Algebra.Smooth.comp k R S
    let : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing k S
    let : IsOpenImmersion (Spec.map (CommRingCat.ofHom φ.toRingHom)) := IsOpenImmersion.of_isLocalization r
    have hI' : Relative.DifferentialBlowup.Construction.firstRelativeDifferentialIdeal k (I.map φ.toRingHom) = ⊤ := by
      change Relative.DifferentialBlowup.Construction.firstRelativeDifferentialIdeal k (I.map (algebraMap R S)) = ⊤
      rw [← Blowups.Smooth.DifferentialNaturality.Construction.smooth_firstRelativeDifferentialIdeal_baseChange k I, hI, Ideal.map_top]
    obtain ⟨P, hP⟩ := Blowups.Etale.RefinementHelpers.Construction.exists_localization_away_prime r (⟨q, inferInstance⟩ : PrimeSpectrum R) hr
    have hIP : I.map φ.toRingHom ≤ P.asIdeal := by
      rw [Ideal.map_le_iff_le_comap]
      exact hIq.trans_eq (congrArg PrimeSpectrum.asIdeal hP).symm
    obtain ⟨C⟩ := UnitBoundaryNormalCenter.Construction.curve_center_unit_boundary_chart (.of S)
      ((HypersurfaceDimension.Construction.localization_ringKrullDim_le (B := S) (Submonoid.powers r)).trans hd)
      (I.map φ.toRingHom) hI' (fun j => φ (w j)) hunit P hIP
    exact ⟨∅, ⟨C.comp (R := R) (S := .of S) I w ∅ φ ⟨q, inferInstance⟩ hP⟩⟩

end

end OAI.AlgebraicGeometry.Resolution.Blowups
