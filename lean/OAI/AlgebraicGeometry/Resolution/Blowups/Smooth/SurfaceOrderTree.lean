import OAI.AlgebraicGeometry.Resolution.Blowups.Surface.OrderOpenChart
import OAI.AlgebraicGeometry.Resolution.Blowups.Curve.CenterPointedFrame

/-! # Surface Order Tree -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.SurfaceOrderTree.Construction

noncomputable section

/-! Finite actual maximal-order reduction on arbitrary smooth affine surfaces. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable (k : Type u) [Field k] [CharZero k] [IsAlgClosed k]
  (R : CommRingCat.{u}) [Algebra k R] [Algebra.Smooth k R]

/-- A finite differential bound supplies an actual open order-reduction
chart at every prime of a smooth affine surface. -/
theorem smooth_surface_order_open_chart_at (hd : ringKrullDim R ≤ 2)
    (J : Ideal R) (n : ℕ) (hbound : Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J (n + 1) = ⊤)
    (q : PrimeSpectrum R) :
    ∃ C : Surface.OrderOpenChart.Construction.SurfaceOrderOpenChart k R J (n + 1), q ∈ C.openRange := by
  classical
  let I := Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J n
  by_cases hIq : I ≤ q.asIdeal
  · have hI : Relative.DifferentialBlowup.Construction.firstRelativeDifferentialIdeal k I = ⊤ :=
      (Curve.IntrinsicStep.Construction.first_iteratedRelativeDifferentialIdeal k J n).trans hbound
    obtain ⟨D, z, hDz⟩ := Curve.CenterPointedFrame.Construction.exists_derivative_outside_center_prime k I q.asIdeal hIq hI
    exact Surface.OrderOpenChart.Construction.surface_derivative_order_open_chart k R hd J n D z.val z.property q hDz
  · obtain ⟨a, ha, haq⟩ : ∃ a ∈ I, a ∉ q.asIdeal := by
      by_contra! h
      exact hIq h
    let S := Localization.Away a
    let f : R →ₐ[k] S := IsScalarTower.toAlgHom k R S
    have hf : f.toRingHom.Etale := RingHom.etale_algebraMap.mpr (Algebra.Etale.of_isLocalizationAway a)
    have ht : Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k (J.map f.toRingHom) n = ⊤ := by
      rw [← DifferentialMap.Construction.smooth_iteratedRelativeDifferentialIdeal_map k f hf J n]
      exact Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_map_of_mem f.toRingHom ha)
        (IsLocalization.Away.algebraMap_isUnit a)
    let T : AffineEtaleControlTree.Construction.SmoothAffineEtaleControlTree k (n + 1) (.of S) (J.map f.toRingHom) :=
      .terminal (by simpa only [Nat.add_sub_cancel] using ht)
    let C : Surface.OrderOpenChart.Construction.SurfaceOrderOpenChart k R J (n + 1) :=
      ⟨.of S, inferInstance, f, IsOpenImmersion.of_isLocalization a, T⟩
    obtain ⟨P, hP⟩ := Blowups.Etale.RefinementHelpers.Construction.exists_localization_away_prime a q haq
    refine ⟨C, ?_⟩
    change q ∈ Set.range (PrimeSpectrum.comap (algebraMap R S))
    exact ⟨P, hP⟩

/-- Every bounded ideal on a smooth affine surface has a finite tree of
actual permissible smooth blowups and finite jointly surjective étale
refinements whose leaves have strictly lower maximal order. -/
theorem exists_smooth_surface_order_reduction_tree (hd : ringKrullDim R ≤ 2)
    (J : Ideal R) (n : ℕ) (hbound : Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J (n + 1) = ⊤) :
    Nonempty (AffineEtaleControlTree.Construction.SmoothAffineEtaleControlTree k (n + 1) R J) := by
  classical
  choose C hC using smooth_surface_order_open_chart_at k R hd J n hbound
  have hcover : Set.univ ⊆ ⋃ p, ((C p).openRange : Set (PrimeSpectrum R)) := by
    intro p _
    exact Set.mem_iUnion.mpr ⟨p, hC p⟩
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover
    (fun p => ((C p).openRange : Set (PrimeSpectrum R))) (fun p => (C p).openRange.isOpen) hcover
  have hsurj (p : PrimeSpectrum R) : ∃ i : s, ∃ q : PrimeSpectrum (C i.val).carrier,
      PrimeSpectrum.comap (C i.val).map.toRingHom q = p := by
    obtain ⟨i, hi, hp⟩ := Set.mem_iUnion₂.mp (hs (Set.mem_univ p))
    exact ⟨⟨i, hi⟩, hp⟩
  have het (i : s) : (C i.val).map.toRingHom.Etale := by
    have h : Etale (Spec.map (CommRingCat.ofHom (C i.val).map.toRingHom)) := inferInstance
    exact (HasRingHomProperty.Spec_iff (P := @Etale)).mp h
  exact ⟨.refineEtale s (fun i => (C i.val).carrier) (fun i => (C i.val).map)
    het hsurj (fun i => (C i.val).tree)⟩

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.SurfaceOrderTree.Construction
