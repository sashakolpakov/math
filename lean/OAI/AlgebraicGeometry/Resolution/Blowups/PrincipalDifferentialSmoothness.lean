import OAI.AlgebraicGeometry.Resolution.Blowups.Relative.DifferentialBlowup
import OAI.AlgebraicGeometry.Resolution.Blowups.DifferentialHypersurfaceNeighborhood
import OAI.AlgebraicGeometry.Resolution.Blowups.LocalizedCenterSmoothness

/-! # Principal Differential Smoothness -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.PrincipalDifferentialSmoothness.Construction

noncomputable section

/-! A unit first differential ideal makes an actual principal hypersurface smooth. -/

universe u

variable (k : Type u) {R : Type u} [CommRing k] [CommRing R] [Algebra k R]

theorem firstRelativeDifferentialIdeal_principal (z : R) :
    Relative.DifferentialBlowup.Construction.firstRelativeDifferentialIdeal k (Ideal.span {z}) =
      Ideal.span {z} ⊔ Ideal.span (Set.range (fun D : Derivation k R R => D z)) := by
  apply le_antisymm
  · apply sup_le le_sup_left
    apply Ideal.span_le.mpr
    rintro _ ⟨⟨D, a⟩, rfl⟩
    have h := Relative.DifferentialBlowup.Construction.relative_derivation_of_span k D (fun _ : Unit => z) (x := a.val) (by
      simpa only [Set.range_const] using a.property)
    have he : Ideal.span (Set.range (fun _ : Unit => D z)) ≤
        Ideal.span (Set.range (fun E : Derivation k R R => E z)) := by
      apply Ideal.span_le.mpr
      rintro _ ⟨_, rfl⟩
      exact Ideal.subset_span ⟨D, rfl⟩
    change D a.val ∈ Ideal.span {z} ⊔ Ideal.span (Set.range (fun E : Derivation k R R => E z))
    simp only [Set.range_const] at h he
    exact (sup_le_sup (le_rfl : Ideal.span {z} ≤ Ideal.span {z}) he) h
  · apply sup_le (Relative.DifferentialBlowup.Construction.le_firstRelativeDifferentialIdeal k _)
    apply Ideal.span_le.mpr
    rintro _ ⟨D, rfl⟩
    exact Relative.DifferentialBlowup.Construction.relative_derivation_mem_first k _ D (Ideal.mem_span_singleton_self z)

theorem smooth_principal_quotient_of_firstDifferential_top [Algebra.Smooth k R]
    (z : R) (h : Relative.DifferentialBlowup.Construction.firstRelativeDifferentialIdeal k (Ideal.span {z}) = ⊤) :
    Algebra.Smooth k (R ⧸ Ideal.span {z}) := by
  let s := Set.range (fun D : Derivation k R R => D z)
  have hs : Ideal.span ((Ideal.Quotient.mk (Ideal.span {z})) '' s) = ⊤ := by
    have he := congrArg (Ideal.map (Ideal.Quotient.mk (Ideal.span {z}))) h
    rw [firstRelativeDifferentialIdeal_principal, Ideal.map_sup, Ideal.map_quotient_self,
      bot_sup_eq, Ideal.map_span, Ideal.map_top] at he
    exact he
  apply LocalizedCenterSmoothness.Construction.smooth_quotient_of_localized_quotients k (Ideal.span {z}) s hs
  rintro _ ⟨D, rfl⟩
  rw [Ideal.map_span, Set.image_singleton]
  exact DifferentialHypersurfaceNeighborhood.Construction.differentialHypersurfaceNeighborhood_smooth D z

end

end OAI.AlgebraicGeometry.Resolution.Blowups.PrincipalDifferentialSmoothness.Construction
