import OAI.AlgebraicGeometry.Resolution.Blowups.LocalizedCenterSmoothness
import OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.AlgebraReduced
import OAI.AlgebraicGeometry.Resolution.Blowups.ZeroDimensionalHypersurfaceCenter
import OAI.AlgebraicGeometry.Resolution.Blowups.HypersurfaceDimension

/-! # Differential Center -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Curve.DifferentialCenter.Construction

noncomputable section

/-! Intrinsic smooth centers on smooth affine curves from the first differential ideal. -/

universe u

variable (k : Type u) {R : Type u} [Field k] [IsAlgClosed k] [CommRing R]
  [Algebra k R] [Algebra.Smooth k R] [Algebra ℚ R] [IsNoetherianRing R]

/-- On a smooth affine ring of dimension at most one, a unit first
differential ideal makes the original closed center smooth. Local equations
are chosen only to prove this property of the fixed ideal. -/
theorem curve_center_smooth_of_first_differential_top
    (hd : ringKrullDim R ≤ 1) (I : Ideal R) (hI : Relative.DifferentialBlowup.Construction.firstRelativeDifferentialIdeal k I = ⊤) :
    Algebra.Smooth k (R ⧸ I) := by
  let s : Set R := Set.range (fun t : Derivation k R R × I => t.1 t.2.val)
  have hs : Ideal.span ((Ideal.Quotient.mk I) '' s) = ⊤ := by
    have h := congrArg (Ideal.map (Ideal.Quotient.mk I)) hI
    change (I ⊔ Ideal.span s).map (Ideal.Quotient.mk I) = (⊤ : Ideal R).map _ at h
    rw [Ideal.map_sup, Ideal.map_quotient_self, bot_sup_eq, Ideal.map_span, Ideal.map_top] at h
    exact h
  apply LocalizedCenterSmoothness.Construction.smooth_quotient_of_localized_quotients k I s hs
  rintro _ ⟨⟨D, z⟩, rfl⟩
  let A := DifferentialHypersurfaceNeighborhood.Construction.derivationNeighborhood D z.val
  let H := DifferentialHypersurfaceNeighborhood.Construction.differentialHypersurfaceNeighborhood D z.val
  let : Algebra.Smooth k H := DifferentialHypersurfaceNeighborhood.Construction.differentialHypersurfaceNeighborhood_smooth D z.val
  let : IsReduced H := Blowups.Smooth.AlgebraReduced.Construction.smooth_algebra_isReduced k
  have hdH : ringKrullDim H ≤ 0 :=
    HypersurfaceDimension.Construction.differentialHypersurfaceNeighborhood_dimension_induction D z.val 0 (by simpa using hd)
  exact ZeroDimensionalHypersurfaceCenter.Construction.zero_dimensional_hypersurface_center_smooth k (algebraMap R A z.val) hdH
    (I.map (algebraMap R A)) (Ideal.mem_map_of_mem _ z.property)

/-- The same intrinsic center is reduced; its scheme structure contains no
extra nilpotent thickening. -/
theorem curve_center_radical_of_first_differential_top
    (hd : ringKrullDim R ≤ 1) (I : Ideal R) (hI : Relative.DifferentialBlowup.Construction.firstRelativeDifferentialIdeal k I = ⊤) :
    I.IsRadical := by
  let : Algebra.Smooth k (R ⧸ I) := curve_center_smooth_of_first_differential_top k hd I hI
  exact (Ideal.isRadical_iff_quotient_reduced I).mpr (Blowups.Smooth.AlgebraReduced.Construction.smooth_algebra_isReduced k)

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Curve.DifferentialCenter.Construction
