import OAI.AlgebraicGeometry.Resolution.Blowups.FlatQuotientRegularity
import OAI.AlgebraicGeometry.Resolution.Blowups.TransverseCoordinateBoundaryTransform
import OAI.AlgebraicGeometry.Resolution.Blowups.ControlledTransformMap
import Mathlib.AlgebraicGeometry.Morphisms.Flat

/-! # Transverse Boundary Flat Transform -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.TransverseBoundaryFlatTransform.Construction

noncomputable section

/-! Transverse boundary ideal quotients on actual flat base changes of blowup charts. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.MvPolynomial

universe u

theorem blowupChartMap_flat {R S : Type u} [CommRing R] [CommRing S]
    (I : Ideal R) (a : I) (φ : R →+* S) (hφ : φ.Flat) :
    (ChartLift.Construction.blowupChartMap I φ a).Flat := by
  let : Algebra R S := φ.toAlgebra
  let : Module.Flat R S := hφ
  let : Flat (Spec.map (CommRingCat.ofHom φ)) :=
    (HasRingHomProperty.Spec_iff (P := @Flat)).mpr hφ
  exact (HasRingHomProperty.Spec_iff (P := @Flat)).mp
    (MorphismProperty.of_isPullback (P := @Flat)
      (ChartFlatBaseChange.Construction.blowupChart_flat_isPullback (S := S) I a).flip inferInstance)

theorem blowupChartMap_transverse_controlled {R S : Type u} [CommRing R] [CommRing S]
    (I J : Ideal R) (a : I) (φ : R →+* S) (hφ : φ.Flat)
    (hJ : ControlledTransform.Construction.blowupControlledTransform I J 1 a = J.map (Blowup.Charts.Construction.blowupChartConstants I a)) :
    ControlledTransform.Construction.blowupControlledTransform (I.map φ) (J.map φ) 1
      ⟨φ a.val, Ideal.mem_map_of_mem φ a.property⟩ =
        (J.map φ).map (Blowup.Charts.Construction.blowupChartConstants (I.map φ)
          ⟨φ a.val, Ideal.mem_map_of_mem φ a.property⟩) := by
  let ψ := ChartLift.Construction.blowupChartMap I φ a
  let : Algebra (Blowup.Charts.Construction.blowupChart I a)
      (Blowup.Charts.Construction.blowupChart (I.map φ) ⟨φ a.val, Ideal.mem_map_of_mem φ a.property⟩) := ψ.toAlgebra
  let : Module.Flat (Blowup.Charts.Construction.blowupChart I a)
      (Blowup.Charts.Construction.blowupChart (I.map φ) ⟨φ a.val, Ideal.mem_map_of_mem φ a.property⟩) :=
    blowupChartMap_flat I a φ hφ
  have h := FlatQuotientRegularity.Construction.flat_map_colon_self
    (S := Blowup.Charts.Construction.blowupChart (I.map φ) ⟨φ a.val, Ideal.mem_map_of_mem φ a.property⟩)
    (J.map (Blowup.Charts.Construction.blowupChartConstants I a))
    (Blowup.Charts.Construction.blowupChartConstants I a a.val) (by
      rw [ControlledTransform.Construction.blowupControlledTransform, pow_one (Blowup.Charts.Construction.blowupChartConstants I a a.val)] at hJ
      exact hJ)
  change ((J.map (Blowup.Charts.Construction.blowupChartConstants I a)).map ψ).colon
    (Ideal.span {ψ (Blowup.Charts.Construction.blowupChartConstants I a a.val)} : Set _) =
      (J.map (Blowup.Charts.Construction.blowupChartConstants I a)).map ψ at h
  dsimp only [ψ] at h
  rw [ControlledTransformMap.Construction.blowupChartMap_totalIdeal, ChartLift.Construction.blowupChartMap_constants] at h
  rw [ControlledTransform.Construction.blowupControlledTransform, pow_one (Blowup.Charts.Construction.blowupChartConstants (I.map φ)
    ⟨φ a.val, Ideal.mem_map_of_mem φ a.property⟩ (φ a.val))]
  exact h

theorem subsetCoordinateBlowup_flat_transverse_boundary_controlled
    {k σ S : Type u} [CommRing k] [IsDomain k] [DecidableEq σ] [CommRing S]
    (C : Finset σ) (i : C) (j : σ) (hj : j ∉ C)
    (φ : MvPolynomial σ k →+* S) (hφ : φ.Flat) :
    ControlledTransform.Construction.blowupControlledTransform ((SubsetCoordinateBlowup.Construction.subsetCoordinateIdeal (R := k) C).map φ)
      (Ideal.span {φ (X j)}) 1
      ⟨φ (X i.val), Ideal.mem_map_of_mem φ (SubsetCoordinateBlowup.Construction.subsetCoordinateElement (R := k) C i).property⟩ =
        Ideal.span {Blowup.Charts.Construction.blowupChartConstants ((SubsetCoordinateBlowup.Construction.subsetCoordinateIdeal (R := k) C).map φ)
          ⟨φ (X i.val), Ideal.mem_map_of_mem φ (SubsetCoordinateBlowup.Construction.subsetCoordinateElement (R := k) C i).property⟩
          (φ (X j))} := by
  have h := blowupChartMap_transverse_controlled (SubsetCoordinateBlowup.Construction.subsetCoordinateIdeal (R := k) C)
    (Ideal.span {X j}) (SubsetCoordinateBlowup.Construction.subsetCoordinateElement (R := k) C i) φ hφ (by
      simpa only [Ideal.map_span, Set.image_singleton] using
        TransverseCoordinateBoundaryTransform.Construction.subsetCoordinateBlowup_transverse_boundary_controlled C i j hj)
  simpa only [Ideal.map_span, Set.image_singleton] using h

end

end OAI.AlgebraicGeometry.Resolution.Blowups.TransverseBoundaryFlatTransform.Construction
