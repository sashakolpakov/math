import OAI.AlgebraicGeometry.Resolution.Blowups.OpenCoefficientTreeLift
import OAI.AlgebraicGeometry.Resolution.Blowups.Affine.CurveFramedOpen

/-! # Curve Coefficient -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Retracted.CurveCoefficient.Construction

noncomputable section

/-! Finite ambient order reduction using an integral curve as the retained hypersurface. -/

open _root_.Polynomial _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

/-- The zero coefficient ideal is handled by the empty coordinate frame.
Its lifted ambient center is the maximal-contact hypersurface itself. -/
theorem exists_zero_ideal_framed_coefficient_tree (k : Type u) [CommRing k]
    (b : ℕ) (hb : 0 < b) (H : CommRingCat.{u}) [Algebra k H] :
    ∃ T : Affine.FramedOpenControlTree.Construction.AffineFramedOpenControlTree k b H ⊥, T.blowupDepth ≤ 1 := by
  classical
  let g : ULift.{u} Empty → H := fun i => nomatch i.down
  let D : ULift.{u} Empty → Derivation k H H := fun i => nomatch i.down
  refine ⟨.blowup (ULift.{u} Empty) g D (by intro i; exact Empty.elim i.down)
    hb bot_le (fun i => nomatch i.down), ?_⟩
  simp [Affine.FramedOpenControlTree.Construction.AffineFramedOpenControlTree.blowupDepth]

variable (k : Type u) [Field k] [CharZero k] [IsAlgClosed k]
  (H R : CommRingCat.{u}) [Algebra k H] [Algebra k R] [Algebra H R] [IsScalarTower k H R]
  [Algebra H[X] R] [IsScalarTower H H[X] R] [Algebra.Etale H[X] R]
  [Algebra.Smooth k H] [Algebra.Smooth k R]

/-- A finite differential bound on the retained curve coefficient ideal
constructs a finite tree of actual smooth ambient blowups and étale covers,
with depth bounded by that coefficient bound. -/
theorem exists_bounded_retracted_curve_coefficient_resolution {ι : Type u}
    (hd : ringKrullDim H ≤ 1)
    (e : (R ⧸ Ideal.span {algebraMap H[X] R X}) ≃ₐ[H] H)
    (p : ι → R) (n m : ℕ) (C : Ideal (R ⧸ Ideal.span {algebraMap H[X] R X}))
    (hlow : WeightedGeneratorFamily.Construction.weightedCoordinateDerivativeFamilyIdeal
      (CoefficientStep.Construction.etaleLineOriginalNormalDerivation k (H := H) (R := R))
      (algebraMap H[X] R X) p (n + 1) ≤ C)
    (hupp : C ≤ Relative.CoefficientIdeal.Construction.relativeCoefficientIdeal k (algebraMap H[X] R X) (Ideal.span (Set.range p)) (n + 1))
    (hz : algebraMap H[X] R X ∈ Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k (Ideal.span (Set.range p)) n)
    (hbound : Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k (C.map e.toRingHom) m = ⊤) :
    ∃ S : Blowups.Smooth.AffineEtaleControlTree.Construction.SmoothAffineEtaleControlTree k (n + 1) R (Ideal.span (Set.range p)), S.blowupDepth ≤ m := by
  let : Algebra ℚ H := ((algebraMap k H).comp (algebraMap ℚ k)).toAlgebra
  let : IsNoetherianRing H := Algebra.FiniteType.isNoetherianRing k H
  let : Algebra ℚ R := ((algebraMap k R).comp (algebraMap ℚ k)).toAlgebra
  let : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing k R
  obtain ⟨T, hT⟩ := Affine.CurveFramedOpen.Construction.exists_bounded_curve_framed_open_control_tree k (n + 1).factorial
    (Nat.factorial_pos _) m H (C.map e.toRingHom) hd hbound
  obtain ⟨S, hS⟩ := OpenCoefficientTreeLift.Construction.exists_lifted_framed_open_coefficient_tree k T R e p C rfl hlow hupp hz
  exact ⟨S, hS.trans hT⟩

/-- For an integral retained hypersurface of dimension at most one, the
finite ambient tree exists for every coefficient interval, including zero.
Every leaf has empty ambient order locus at the original control. -/
theorem exists_retracted_integral_curve_coefficient_resolution [IsDomain H] {ι : Type u}
    (hd : ringKrullDim H ≤ 1)
    (e : (R ⧸ Ideal.span {algebraMap H[X] R X}) ≃ₐ[H] H)
    (p : ι → R) (n : ℕ) (C : Ideal (R ⧸ Ideal.span {algebraMap H[X] R X}))
    (hlow : WeightedGeneratorFamily.Construction.weightedCoordinateDerivativeFamilyIdeal
      (CoefficientStep.Construction.etaleLineOriginalNormalDerivation k (H := H) (R := R))
      (algebraMap H[X] R X) p (n + 1) ≤ C)
    (hupp : C ≤ Relative.CoefficientIdeal.Construction.relativeCoefficientIdeal k (algebraMap H[X] R X) (Ideal.span (Set.range p)) (n + 1))
    (hz : algebraMap H[X] R X ∈ Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k (Ideal.span (Set.range p)) n) :
    Nonempty (Blowups.Smooth.AffineEtaleControlTree.Construction.SmoothAffineEtaleControlTree k (n + 1) R (Ideal.span (Set.range p))) := by
  classical
  by_cases hzero : C.map e.toRingHom = ⊥
  · let : Algebra ℚ R := ((algebraMap k R).comp (algebraMap ℚ k)).toAlgebra
    let : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing k R
    obtain ⟨T, _⟩ := exists_zero_ideal_framed_coefficient_tree k (n + 1).factorial (Nat.factorial_pos _) H
    obtain ⟨S, _⟩ := OpenCoefficientTreeLift.Construction.exists_lifted_framed_open_coefficient_tree k T R e p C hzero hlow hupp hz
    exact ⟨S⟩
  · obtain ⟨m, hm⟩ := Blowups.Smooth.DifferentialOrderBound.Construction.exists_smooth_relative_differential_order_bound k (C.map e.toRingHom) hzero
    obtain ⟨S, _⟩ := exists_bounded_retracted_curve_coefficient_resolution k H R hd e p n m C hlow hupp hz hm
    exact ⟨S⟩

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Retracted.CurveCoefficient.Construction
