import OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.IntegralOpenCover
import OAI.AlgebraicGeometry.Resolution.Blowups.Retracted.CurveCoefficient

/-! # Curve Coefficient -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.CurveCoefficient.Construction

noncomputable section

/-! Coefficient resolution on arbitrary smooth affine curves, including zero ideals and disconnected rings. -/

open _root_.Polynomial _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable (k : Type u) [Field k] [CharZero k] [IsAlgClosed k]

/-- Every ideal on a smooth affine curve admits a finite framed coefficient
tree at every positive control. Integral open charts handle nonzero ideals by
finite differential bounds and zero ideals by the empty coefficient frame. -/
theorem exists_smooth_curve_framed_coefficient_tree (b : ℕ) (hb : 0 < b)
    (H : CommRingCat.{u}) [Algebra k H] [Algebra.Smooth k H]
    (C : Ideal H) (hd : ringKrullDim H ≤ 1) :
    Nonempty (Affine.FramedOpenControlTree.Construction.AffineFramedOpenControlTree k b H C) := by
  classical
  obtain ⟨s, A, hcover⟩ := IntegralOpenCover.Construction.exists_finite_smooth_integral_open_cover k (R := H)
  have hchildren (i : s) : Nonempty (Affine.FramedOpenControlTree.Construction.AffineFramedOpenControlTree k b (A i).carrier
      (C.map (A i).map.toRingHom)) := by
    have hdim : ringKrullDim (A i).carrier ≤ 1 :=
      (Affine.OpenDimension.Construction.ringKrullDim_le_of_spec_openImmersion (A i).map.toRingHom).trans hd
    by_cases hzero : C.map (A i).map.toRingHom = ⊥
    · obtain ⟨T, _⟩ := Retracted.CurveCoefficient.Construction.exists_zero_ideal_framed_coefficient_tree k b hb (A i).carrier
      rw [hzero]
      exact ⟨T⟩
    · exact Affine.CurveFramedOpen.Construction.exists_curve_framed_open_control_tree k b hb (A i).carrier _ hdim hzero
  have hsurj (p : PrimeSpectrum H) : ∃ i : s, ∃ q : PrimeSpectrum (A i).carrier,
      PrimeSpectrum.comap (A i).map.toRingHom q = p := by
    have hp : p ∈ ⨆ i, (A i).openRange := by rw [hcover]; trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hp
    exact ⟨i, hi⟩
  exact ⟨.refineOpen s (fun i => (A i).carrier) (fun i => (A i).map)
    (fun i => (A i).isOpenImmersion) hsurj (fun i => (hchildren i).some)⟩

/-- A retained smooth hypersurface of dimension at most one always gives
a finite ambient order-reduction tree. Neither the hypersurface ring nor
its coefficient ideal is assumed integral or nonzero. -/
theorem exists_retracted_smooth_curve_coefficient_resolution
    (H R : CommRingCat.{u}) [Algebra k H] [Algebra k R] [Algebra H R] [IsScalarTower k H R]
    [Algebra H[X] R] [IsScalarTower H H[X] R] [Algebra.Etale H[X] R]
    [Algebra.Smooth k H] [Algebra.Smooth k R] {ι : Type u}
    (hd : ringKrullDim H ≤ 1)
    (e : (R ⧸ Ideal.span {algebraMap H[X] R X}) ≃ₐ[H] H)
    (p : ι → R) (n : ℕ) (C : Ideal (R ⧸ Ideal.span {algebraMap H[X] R X}))
    (hlow : WeightedGeneratorFamily.Construction.weightedCoordinateDerivativeFamilyIdeal
      (Retracted.CoefficientStep.Construction.etaleLineOriginalNormalDerivation k (H := H) (R := R))
      (algebraMap H[X] R X) p (n + 1) ≤ C)
    (hupp : C ≤ Relative.CoefficientIdeal.Construction.relativeCoefficientIdeal k (algebraMap H[X] R X) (Ideal.span (Set.range p)) (n + 1))
    (hz : algebraMap H[X] R X ∈ Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k (Ideal.span (Set.range p)) n) :
    Nonempty (AffineEtaleControlTree.Construction.SmoothAffineEtaleControlTree k (n + 1) R (Ideal.span (Set.range p))) := by
  let : Algebra ℚ R := ((algebraMap k R).comp (algebraMap ℚ k)).toAlgebra
  let : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing k R
  obtain ⟨T⟩ := exists_smooth_curve_framed_coefficient_tree k (n + 1).factorial
    (Nat.factorial_pos _) H (C.map e.toRingHom) hd
  obtain ⟨S, _⟩ := OpenCoefficientTreeLift.Construction.exists_lifted_framed_open_coefficient_tree k T R e p C rfl hlow hupp hz
  exact ⟨S⟩

/-- Intrinsic coefficient ideals supply the required interval automatically.
Thus every maximal-contact equation with a smooth curve as its retained
hypersurface gives a finite actual ambient tree for the original ideal. -/
theorem exists_retracted_curve_maximal_contact_tree
    (H R : CommRingCat.{u}) [Algebra k H] [Algebra k R] [Algebra H R] [IsScalarTower k H R]
    [Algebra H[X] R] [IsScalarTower H H[X] R] [Algebra.Etale H[X] R]
    [Algebra.Smooth k H] [Algebra.Smooth k R]
    (hd : ringKrullDim H ≤ 1)
    (e : (R ⧸ Ideal.span {algebraMap H[X] R X}) ≃ₐ[H] H)
    (J : Ideal R) (n : ℕ)
    (hz : algebraMap H[X] R X ∈ Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J n) :
    Nonempty (AffineEtaleControlTree.Construction.SmoothAffineEtaleControlTree k (n + 1) R J) := by
  let p : J → R := Subtype.val
  have hspan : Ideal.span (Set.range p) = J := by
    rw [Subtype.range_val, Ideal.span_eq]
  rw [← hspan]
  apply exists_retracted_smooth_curve_coefficient_resolution k H R hd e p n
    (Relative.CoefficientIdeal.Construction.relativeCoefficientIdeal k (algebraMap H[X] R X) (Ideal.span (Set.range p)) (n + 1))
  · exact Relative.CoefficientFamilyInterval.Construction.weightedCoordinateDerivativeFamilyIdeal_le_relative k
      (Retracted.CoefficientStep.Construction.etaleLineOriginalNormalDerivation k (H := H) (R := R)) (algebraMap H[X] R X) p (n + 1)
  · exact le_rfl
  · simpa only [hspan] using hz

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.CurveCoefficient.Construction
