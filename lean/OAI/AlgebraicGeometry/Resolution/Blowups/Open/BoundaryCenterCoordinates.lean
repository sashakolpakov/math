import OAI.AlgebraicGeometry.Resolution.Blowups.Coordinate.CenterChartComposition
import OAI.AlgebraicGeometry.Resolution.Blowups.Boundary.CenterCoordinateCompletion

/-! # Boundary Center Coordinates -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Open.BoundaryCenterCoordinates.Construction

noncomputable section

/-! Descend a coordinate-center chart from an actual open with exact boundary derivations. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable (k : Type u) [CommRing k]

theorem exists_boundary_center_coordinates_of_open_dual_frame
    (R S : CommRingCat.{u}) [Algebra k R] [Algebra k S] [Algebra.Smooth k R]
    (f : R →ₐ[k] S) [IsOpenImmersion (Spec.map (CommRingCat.ofHom f.toRingHom))]
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    (g : ι → R) (D : ι → Derivation k R R)
    (hD : ∀ i j, D i (g j) = if i = j then 1 else 0)
    {n : ℕ} (w : Fin n → R) (E : Fin n → Derivation k S S)
    (hE : ∀ i j, E i (f (w j)) = if i = j then 1 else 0)
    (hw : ∀ j, w j ∈ Ideal.span (Set.range g))
    (p : PrimeSpectrum R) (hp : Ideal.span (Set.range g) ≤ p.asIdeal)
    (q : PrimeSpectrum S) (hq : PrimeSpectrum.comap f.toRingHom q = p) :
    Nonempty (Boundary.CoordinateCenterChart.Construction.BoundaryCoordinateCenterOpenChart k R (Ideal.span (Set.range g)) w p) := by
  have het : Etale (Spec.map (CommRingCat.ofHom f.toRingHom)) := inferInstance
  have hf : f.toRingHom.Etale := (HasRingHomProperty.Spec_iff (P := @Etale)).mp het
  let : Algebra.Smooth k S := Blowups.Etale.RefinementHelpers.Construction.smooth_target_of_etale_algHom k f hf
  let g' : ι → S := fun j => f (g j)
  let D' : ι → Derivation k S S := fun j => Blowups.Etale.DerivationHom.Construction.extendEtaleRingDerivationHom k f.toRingHom hf f.commutes (D j)
  have hDapply (i : ι) (r : R) : D' i (f r) = f (D i r) :=
    Blowups.Etale.DerivationHom.Construction.extendEtaleRingDerivationHom_apply k f.toRingHom hf f.commutes (D i) r
  have hD' : ∀ i j, D' i (g' j) = if i = j then 1 else 0 := by
    intro i j
    change D' i (f (g j)) = _
    rw [hDapply, hD]
    split_ifs <;> simp
  have hspan : Ideal.span (Set.range g') = (Ideal.span (Set.range g)).map f.toRingHom := by
    rw [Ideal.map_span, ← Set.range_comp]
    rfl
  have hqI : q.asIdeal.comap f.toRingHom = p.asIdeal := congrArg PrimeSpectrum.asIdeal hq
  have hp' : Ideal.span (Set.range g') ≤ q.asIdeal := by
    rw [hspan, Ideal.map_le_iff_le_comap, hqI]
    exact hp
  have hw' (j : Fin n) : f (w j) ∈ Ideal.span (Set.range g') := by
    rw [hspan]
    exact Ideal.mem_map_of_mem f.toRingHom (hw j)
  obtain ⟨C⟩ := Boundary.CenterCoordinateCompletion.Construction.exists_boundary_coordinate_center_open_chart k S g' D' hD'
    (fun j => f (w j)) E hE hw' q hp'
  have C' : Boundary.CoordinateCenterChart.Construction.BoundaryCoordinateCenterOpenChart k S
      ((Ideal.span (Set.range g)).map f.toRingHom) (fun j => f (w j)) q := by
    rw [← hspan]
    exact C
  exact ⟨Boundary.CoordinateCenterChart.Construction.BoundaryCoordinateCenterOpenChart.comp f (Ideal.span (Set.range g)) w p q hq C'⟩

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Open.BoundaryCenterCoordinates.Construction
