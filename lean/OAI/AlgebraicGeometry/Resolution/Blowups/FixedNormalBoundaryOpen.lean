import OAI.AlgebraicGeometry.Resolution.Blowups.Modeled.FixedTransverseCoordinates
import OAI.AlgebraicGeometry.Resolution.Blowups.ActiveModeledBoundaryChart
import OAI.AlgebraicGeometry.Resolution.Blowups.Boundary.Coordinates
import OAI.AlgebraicGeometry.Resolution.Blowups.Boundary.UnitLabelsUnused
import OAI.AlgebraicGeometry.Resolution.Blowups.TransverseBoundaryOpen
import OAI.AlgebraicGeometry.Resolution.Blowups.RefinedNormalOpen

/-! # Fixed Normal Boundary Open -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.FixedNormalBoundaryOpen.Construction

noncomputable section

/-! Adapt the full boundary to a specified normal equation without replacing that equation. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u v

/-- A boundary-tangent derivative taking the given equation to one
supplies actual pointed coordinates retaining that equation and every
original boundary label. This includes labels absent from the point. -/
theorem exists_fixed_normal_boundary_open
    {k : Type u} [Field k] (R : CommRingCat.{u}) [Algebra k R]
    {ι : Type v} [Fintype ι] (w : ι → R) (M : Etale.BoundaryModel.Construction.EtaleBoundaryModel k R ι w)
    (E : Derivation k R R) (hE : E ∈ Relative.LogarithmicIdeal.Construction.relativeLogarithmicDerivations k w)
    (z : R) (hz : E z = 1) (p : PrimeSpectrum R) :
    Nonempty (TransverseBoundaryOpen.Construction.TransverseBoundaryOpenChart k R w z p) := by
  classical
  have hbound : Relative.LogarithmicIdeal.Construction.iteratedRelativeLogarithmicDifferentialIdeal k w (Ideal.span {z}) 1 = ⊤ := by
    change Relative.LogarithmicIdeal.Construction.firstRelativeLogarithmicDifferentialIdeal k w (Ideal.span {z}) = ⊤
    have h := Relative.LogarithmicIdeal.Construction.relative_logarithmic_derivation_mem_first k w (Ideal.span {z})
      ⟨E, hE⟩ (Ideal.mem_span_singleton_self z)
    rw [hz] at h
    exact Ideal.eq_top_of_isUnit_mem _ h isUnit_one
  obtain ⟨C⟩ := ActiveModeledBoundaryChart.Construction.exists_active_modeled_boundary_open_chart R w M (Ideal.span {z}) 1 p hbound
  let A := Localization.Away C.denominator
  let E' := Etale.Derivation.Construction.extendEtaleRingDerivation (S := A) E
  have hEfull : E' ∈ Relative.LogarithmicIdeal.Construction.relativeLogarithmicDerivations k (fun j => algebraMap R A (w j)) :=
    Relative.LogarithmicBoundary.Construction.extendEtaleRingDerivation_relative_logarithmic (S := A) k w ⟨E, hE⟩
  have hEa : E' ∈ Relative.LogarithmicIdeal.Construction.relativeLogarithmicDerivations k
      (fun j : C.active => algebraMap R A (w j.val)) := fun j => hEfull j.val
  have hza : E' (algebraMap R A z) = 1 := by
    change Etale.Derivation.Construction.extendEtaleRingDerivation (S := A) E (algebraMap R A z) = 1
    rw [Etale.Derivation.Construction.extendEtaleRingDerivation_algebraMap, hz, map_one]
  have hzn : E' (algebraMap R A z) ∉ C.point.asIdeal := by
    rw [hza]
    intro h1
    exact C.point.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ h1 isUnit_one)
  obtain ⟨D, f, d, φ, η, hφ, hg, hZ, hW, hη⟩ :=
    Modeled.FixedTransverseCoordinates.Construction.exists_modeled_fixed_transverse_coordinates C.model C.point.asIdeal
      C.active_equations_mem E' hEa (algebraMap R A z) hzn
  let U := Localization.Away f
  let gA : A →ₐ[k] U := IsScalarTower.toAlgHom k A U
  let g : R →ₐ[k] U := gA.comp (IsScalarTower.toAlgHom k R A)
  let e : C.model.boundaryIndices ↪ Fin d ⊕ Option C.model.boundaryIndices :=
    ⟨fun s => Sum.inr (some s), fun _ _ h => Option.some.inj (Sum.inr.inj h)⟩
  let N := C.model.replaceCoordinates gA φ hφ hg e hW
  have hn : ∀ j, N.coordinate j ≠ some (Sum.inr none) :=
    C.model.replaceCoordinates_unused gA φ hφ hg e hW (Sum.inr none) (by
      intro s hs
      have hbad : some s = none := Sum.inr.inj hs
      cases hbad)
  have hu (j : ι) (hj : j ∉ C.active) : IsUnit (g (w j)) :=
    (C.inactive_units j hj).map gA.toRingHom
  let N' := Etale.BoundaryModel.Construction.EtaleBoundaryModel.extendUnitLabels (fun j => g (w j)) C.active N hu
  let : IsOpenImmersion (Spec.map (CommRingCat.ofHom gA.toRingHom)) :=
    RefinedNormalOpen.Construction.refinedNormalOpen_isOpenImmersion D (algebraMap R A z) f
  have ho : IsOpenImmersion (Spec.map (CommRingCat.ofHom g.toRingHom)) := by
    change IsOpenImmersion (Spec.map
      (CommRingCat.ofHom (algebraMap R A) ≫ CommRingCat.ofHom gA.toRingHom))
    rw [Spec.map_comp]
    infer_instance
  obtain ⟨Q, hQ⟩ := RefinedNormalOpen.Construction.refinedNormalOpen_lifts_prime D (algebraMap R A z) f C.point η hη
  have hQI : Q.asIdeal.comap gA.toRingHom = C.point.asIdeal := congrArg PrimeSpectrum.asIdeal hQ
  have hpI : C.point.asIdeal.comap (algebraMap R A) = p.asIdeal :=
    congrArg PrimeSpectrum.asIdeal C.point_over
  have hQp : PrimeSpectrum.comap g.toRingHom Q = p := by
    apply PrimeSpectrum.ext
    change Q.asIdeal.comap (gA.toRingHom.comp (algebraMap R A)) = p.asIdeal
    rw [← Ideal.comap_comap, hQI, hpI]
  let chart : Etale.BoundaryModel.Construction.EtaleBoundaryOpenChart k R w p :=
    { carrier := .of U
      algebra := inferInstance
      map := g
      isOpenImmersion := ho
      point := Q
      point_over := hQp
      model := N' }
  exact ⟨{ chart := chart
           normalIndex := Sum.inr none
           normal_eq := hZ
           normal_unused := N.extendUnitLabels_unused (fun j => g (w j)) C.active hu
             (Sum.inr none) hn }⟩

end

end OAI.AlgebraicGeometry.Resolution.Blowups.FixedNormalBoundaryOpen.Construction
