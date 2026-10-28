import OAI.AlgebraicGeometry.Resolution.Blowups.MixedBoundary.DualFrame
import OAI.AlgebraicGeometry.Resolution.Blowups.Curve.CenterPointedFrame

/-! # Unit Boundary Normal Center -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.UnitBoundaryNormalCenter.Construction

noncomputable section

/-! Normal centers have common boundary coordinates when the boundary equations are units. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u v

theorem normal_center_unit_boundary_chart
    {k : Type u} [CommRing k] (R : CommRingCat.{u}) [Algebra k R] [Algebra.Smooth k R]
    (z : R) (D : Derivation k R R) (hD : D z = 1)
    {β : Type v} (w : β → R) (hw : ∀ j, IsUnit (w j)) (p : PrimeSpectrum R) :
    Nonempty (MixedBoundary.CenterCharts.Construction.MixedBoundaryCoordinateCenterOpenChart k R (Ideal.span {z}) w ∅ p) := by
  classical
  let ι := ULift.{u} Unit
  have hframe : ∀ i j : ι, D z = if i = j then 1 else 0 := by
    intro i j
    rw [ite_eq_left (Subsingleton.elim i j), hD]
  have heq : Coordinate.FamilyIdeal.Construction.coordinateFamilyIdeal (fun _ : ι => z) Finset.univ = Ideal.span {z} := by
    simp only [Coordinate.FamilyIdeal.Construction.coordinateFamilyIdeal, Finset.coe_univ, Set.image_univ, Set.range_const]
  rw [← heq]
  exact MixedBoundary.DualFrame.Construction.mixed_boundary_chart_of_dual_frame R (fun _ : ι => z) (fun _ : ι => D) hframe
    Finset.univ w w hw (fun _ => none) (by intro _ _ _ h; cases h)
    (fun j => (mul_one (w j)).symm) ∅ (by intro j; simp) p

theorem curve_center_unit_boundary_chart
    {k : Type u} [Field k] [IsAlgClosed k] (R : CommRingCat.{u}) [Algebra k R]
    [Algebra.Smooth k R] [Algebra ℚ R] [IsNoetherianRing R]
    (hd : ringKrullDim R ≤ 1) (I : Ideal R) (hI : Relative.DifferentialBlowup.Construction.firstRelativeDifferentialIdeal k I = ⊤)
    {β : Type v} (w : β → R) (hw : ∀ j, IsUnit (w j))
    (p : PrimeSpectrum R) (hp : I ≤ p.asIdeal) :
    Nonempty (MixedBoundary.CenterCharts.Construction.MixedBoundaryCoordinateCenterOpenChart k R I w ∅ p) := by
  obtain ⟨S, aS, f, Q, hQ, hQp, hopen, hsmooth, z, D, hgen, hD⟩ :=
    Curve.CenterPointedFrame.Construction.curve_center_pointed_coordinate_neighborhood k hd I p.asIdeal hp hI
  let : Algebra k S := aS
  let : Algebra.Smooth k S := hsmooth
  let : IsOpenImmersion (Spec.map (CommRingCat.ofHom f.toRingHom)) := hopen
  have hC : Nonempty (MixedBoundary.CenterCharts.Construction.MixedBoundaryCoordinateCenterOpenChart k S (I.map f.toRingHom)
      (fun j => f (w j)) ∅ ⟨Q, hQ⟩) := by
    rw [hgen]
    exact normal_center_unit_boundary_chart S z D hD (fun j => f (w j))
      (fun j => (hw j).map f.toRingHom) ⟨Q, hQ⟩
  obtain ⟨C⟩ := hC
  exact ⟨C.comp I w ∅ f p (PrimeSpectrum.ext hQp)⟩

end

end OAI.AlgebraicGeometry.Resolution.Blowups.UnitBoundaryNormalCenter.Construction
