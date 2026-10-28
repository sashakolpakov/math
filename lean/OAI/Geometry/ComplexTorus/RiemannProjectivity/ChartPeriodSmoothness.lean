import OAI.Geometry.ComplexTorus.RiemannProjectivity.ConeChartMem
import OAI.Geometry.ComplexTorus.RiemannProjectivity.AffineCone

/-! # Chart Period Smoothness -/

namespace OAI

noncomputable section

namespace Geometry.ComplexTorus.RiemannProjectivity.ChartPeriodSmoothness.Constructions.ConeChartSmoothness

/-! # RiemannProjectivity: normalized projective charts inherit smoothness from the cone point -/

open Set
open OAI.Geometry.ComplexTorus.RiemannProjectivity.AffineVanishing.Constructions.AffineVanishingPoints OAI.Geometry.ComplexTorus.RiemannProjectivity.ConeChartBy.Constructions.ConeChartRestriction OAI.Geometry.ComplexTorus.RiemannProjectivity.ConeChartMem.Constructions.ConeChartNormalization
  AlgebraicGeometry.Foundations.Scheme.DehomogenizationC.Algebraic.Dehomogenization SmoothReferencePoint.Constructions.SmoothPointLocalization

variable {ι : Type*} [Fintype ι]

omit [Fintype ι] in
theorem restriction_invSelf (S : Set (ι → ℂ)) (i : ι) :
    ConeChartBy.Constructions.ConeChartRestriction.localizedRestriction S i (IsLocalization.Away.invSelf (ConeChartBy.Constructions.ConeChartRestriction.variableClass S i)) = 1 := by
  have h := congrArg (ConeChartBy.Constructions.ConeChartRestriction.localizedRestriction S i)
    (IsLocalization.Away.mul_invSelf (S := ConeChartBy.Constructions.ConeChartRestriction.patchRing S i) (ConeChartBy.Constructions.ConeChartRestriction.variableClass S i))
  rw [map_mul, ConeChartBy.Constructions.ConeChartRestriction.localizedRestriction_algebraMap, ConeChartBy.Constructions.ConeChartRestriction.restriction_variable_self, one_mul, map_one] at h
  exact h

omit [Fintype ι] in
theorem restriction_ratio (S : Set (ι → ℂ)) (i : ι) (j : {j : ι // j ≠ i}) :
    ConeChartBy.Constructions.ConeChartRestriction.localizedRestriction S i (ConeChartMem.Constructions.ConeChartNormalization.ratio S i j) = Ideal.Quotient.mk _ (MvPolynomial.X j) := by
  rw [ConeChartMem.Constructions.ConeChartNormalization.ratio, map_mul, ConeChartBy.Constructions.ConeChartRestriction.localizedRestriction_algebraMap, ConeChartBy.Constructions.ConeChartRestriction.restriction_variable S i j.val j.property,
    restriction_invSelf, mul_one]

theorem retraction (S : Set (ι → ℂ))
    (hS : ∀ x, (∀ p ∈ MvPolynomial.vanishingIdeal ℂ S, MvPolynomial.eval x p = 0) → x ∈ S)
    (hcone : ∀ (c : ℂ) ⦃w⦄, w ∈ S → c • w ∈ S) (i : ι) :
    (ConeChartBy.Constructions.ConeChartRestriction.localizedRestriction S i).comp (ConeChartMem.Constructions.ConeChartNormalization.normalization S hS hcone i) = AlgHom.id ℂ (AffineVanishing.Constructions.AffineVanishingPoints.coordinateRing (ConeChartBy.Constructions.ConeChartRestriction.chart S i)) := by
  apply Ideal.Quotient.algHom_ext ℂ
  apply MvPolynomial.algHom_ext
  intro j
  change ConeChartBy.Constructions.ConeChartRestriction.localizedRestriction S i (MvPolynomial.aeval (ConeChartMem.Constructions.ConeChartNormalization.ratio S i) (MvPolynomial.X j)) =
    Ideal.Quotient.mk _ (MvPolynomial.X j)
  rw [MvPolynomial.aeval_X, restriction_ratio]

theorem mem_smoothLocus (S : Set (ι → ℂ))
    (hS : ∀ x, (∀ p ∈ MvPolynomial.vanishingIdeal ℂ S, MvPolynomial.eval x p = 0) → x ∈ S)
    (hcone : ∀ (c : ℂ) ⦃w⦄, w ∈ S → c • w ∈ S) (i : ι)
    (x : {j : ι // j ≠ i} → ℂ) (hx : x ∈ ConeChartBy.Constructions.ConeChartRestriction.chart S i)
    (hsm : SmoothReferencePoint.Constructions.SmoothPointLocalization.pointPrime (AffineCone.Constructions.AffineCoordinateSmoothness.point S (AlgebraicGeometry.Foundations.Scheme.DehomogenizationC.Algebraic.Dehomogenization.insertOne i x) hx) ∈
      Algebra.smoothLocus ℂ (AffineVanishing.Constructions.AffineVanishingPoints.coordinateRing S)) :
    SmoothReferencePoint.Constructions.SmoothPointLocalization.pointPrime (AffineCone.Constructions.AffineCoordinateSmoothness.point (ConeChartBy.Constructions.ConeChartRestriction.chart S i) x hx) ∈
      Algebra.smoothLocus ℂ (AffineVanishing.Constructions.AffineVanishingPoints.coordinateRing (ConeChartBy.Constructions.ConeChartRestriction.chart S i)) := by
  let q := AffineCone.Constructions.AffineCoordinateSmoothness.point (ConeChartBy.Constructions.ConeChartRestriction.chart S i) x hx
  let qB := q.comp (ConeChartBy.Constructions.ConeChartRestriction.localizedRestriction S i)
  have heq : qB.comp (Algebra.algHom ℂ (AffineVanishing.Constructions.AffineVanishingPoints.coordinateRing S) (ConeChartBy.Constructions.ConeChartRestriction.patchRing S i)) =
      AffineCone.Constructions.AffineCoordinateSmoothness.point S (AlgebraicGeometry.Foundations.Scheme.DehomogenizationC.Algebraic.Dehomogenization.insertOne i x) hx := by
    apply Ideal.Quotient.algHom_ext ℂ
    apply AlgHom.ext
    intro p
    change q (ConeChartBy.Constructions.ConeChartRestriction.localizedRestriction S i
      (algebraMap (AffineVanishing.Constructions.AffineVanishingPoints.coordinateRing S) (ConeChartBy.Constructions.ConeChartRestriction.patchRing S i) (Ideal.Quotient.mk _ p))) =
        MvPolynomial.eval (AlgebraicGeometry.Foundations.Scheme.DehomogenizationC.Algebraic.Dehomogenization.insertOne i x) p
    rw [ConeChartBy.Constructions.ConeChartRestriction.localizedRestriction_algebraMap]
    change MvPolynomial.eval x (AlgebraicGeometry.Foundations.Scheme.DehomogenizationC.Algebraic.Dehomogenization.dehomogenize i p) = _
    exact AlgebraicGeometry.Foundations.Scheme.DehomogenizationC.Algebraic.Dehomogenization.eval_dehomogenize i p x
  have hqB : SmoothReferencePoint.Constructions.SmoothPointLocalization.pointPrime qB ∈ Algebra.smoothLocus ℂ (ConeChartBy.Constructions.ConeChartRestriction.patchRing S i) := by
    rw [← Algebra.smoothLocus_comap_of_isLocalization (R := ℂ) (Af := ConeChartBy.Constructions.ConeChartRestriction.patchRing S i)
      (ConeChartBy.Constructions.ConeChartRestriction.variableClass S i)]
    change SmoothReferencePoint.Constructions.SmoothPointLocalization.pointPrime (qB.comp (Algebra.algHom ℂ (AffineVanishing.Constructions.AffineVanishingPoints.coordinateRing S) (ConeChartBy.Constructions.ConeChartRestriction.patchRing S i))) ∈
      Algebra.smoothLocus ℂ (AffineVanishing.Constructions.AffineVanishingPoints.coordinateRing S)
    rwa [heq]
  exact AffineCone.Constructions.PointStalkMaps.smooth_retract_at_point (ConeChartMem.Constructions.ConeChartNormalization.normalization S hS hcone i)
    (ConeChartBy.Constructions.ConeChartRestriction.localizedRestriction S i) (retraction S hS hcone i) q hqB

end Geometry.ComplexTorus.RiemannProjectivity.ChartPeriodSmoothness.Constructions.ConeChartSmoothness

namespace Geometry.ComplexTorus.RiemannProjectivity.ChartPeriodSmoothness.Constructions.PeriodChartSmoothness

/-! # RiemannProjectivity: every actual CM period point is smooth in its projective affine chart -/

open Set
open OAI.Geometry.ComplexTorus.RiemannProjectivity.ConeTangentF.Constructions.ConeTangent OAI.Geometry.ComplexTorus.RiemannProjectivity.SmoothReferencePoint.Constructions.SmoothPointLocalization OAI.Geometry.ComplexTorus.RiemannProjectivity.ConeChartBy.Constructions.ConeChartRestriction
  AffineVanishing.Constructions.AffineVanishingPoints AlgebraicGeometry.Foundations.Scheme.DehomogenizationC.Algebraic.Dehomogenization

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
  {n : ℕ}

theorem mem_smoothLocus (Φ : AlgebraicGeometry.ComplexMultiplication.CM.TypeHodgeStructure.CMEmbeddingType E)
    (f : Φ.periodTorus → Projectivization ℂ (Fin (n + 1) → ℂ)) (hf : Topology.IsClosedEmbedding f)
    (hd : ∀ (z : AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E) (i : Fin (n + 1)),
      f (QuotientAddGroup.mk z) ∈ (AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i).source →
      DifferentiableAt ℂ (fun w => AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i (f (QuotientAddGroup.mk w))) z ∧
      Function.Injective (fderiv ℂ (fun w => AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i (f (QuotientAddGroup.mk w))) z))
    (hS : ∀ w, (∀ p ∈ MvPolynomial.vanishingIdeal ℂ (AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.projectiveCone (range f)),
      MvPolynomial.eval w p = 0) → w ∈ AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.projectiveCone (range f))
    (i : Fin (n + 1)) (x : {j : Fin (n + 1) // j ≠ i} → ℂ)
    (hx : x ∈ ConeChartBy.Constructions.ConeChartRestriction.chart (AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.projectiveCone (range f)) i) :
    SmoothReferencePoint.Constructions.SmoothPointLocalization.pointPrime (AffineCone.Constructions.AffineCoordinateSmoothness.point (ConeChartBy.Constructions.ConeChartRestriction.chart (AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.projectiveCone (range f)) i) x hx) ∈
      Algebra.smoothLocus ℂ (AffineVanishing.Constructions.AffineVanishingPoints.coordinateRing (ConeChartBy.Constructions.ConeChartRestriction.chart (AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.projectiveCone (range f)) i)) := by
  apply ConeChartSmoothness.mem_smoothLocus (AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.projectiveCone (range f)) hS
    (AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.smul_mem_projectiveCone (range f)) i x hx
  let v : AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.projectiveCone (range f) := ⟨AlgebraicGeometry.Foundations.Scheme.DehomogenizationC.Algebraic.Dehomogenization.insertOne i x, hx⟩
  have hvi : v.val i = 1 := AlgebraicGeometry.Foundations.Scheme.DehomogenizationC.Algebraic.Dehomogenization.insertOne_self i x
  have hvi0 : v.val i ≠ 0 := hvi ▸ one_ne_zero
  obtain ⟨t, ht⟩ := (AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ConeCharts.Constructions.Cone.mem_projectiveCone_iff_dehomogenize (range f) i v.val hvi0).mp v.property
  obtain ⟨z, hz⟩ := QuotientAddGroup.mk_surjective t
  have htarget : AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ConeCharts.Constructions.Cone.dehomogenize i v.val ∈ (AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i).target := by
    rw [AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart_target]
    trivial
  have hfp : f (QuotientAddGroup.mk z) = (AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i).symm (AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ConeCharts.Constructions.Cone.dehomogenize i v.val) := by
    rw [hz]
    exact ht
  have hi : f (QuotientAddGroup.mk z) ∈ (AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i).source := by
    rw [hfp]
    exact (AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i).symm.map_source htarget
  have hchart : AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i (f (QuotientAddGroup.mk z)) = AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ConeCharts.Constructions.Cone.dehomogenize i v.val := by
    rw [hfp]
    exact (AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i).right_inv htarget
  have hv : v.val = ConeTangentF.Constructions.ConeTangent.parameterization i
      (fun w => AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i (f (QuotientAddGroup.mk w))) (z, 1) := by
    symm
    change ConeTangentF.Constructions.ConeTangent.insertCoordinate i (1, (1 : ℂ) • AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i (f (QuotientAddGroup.mk z))) = v.val
    rw [hchart, ← hvi]
    exact ConeTangentF.Constructions.ConeTangent.insertCoordinate_dehomogenize i v.val hvi0
  exact AffineCone.Constructions.NormalizedConeSmoothness.mem_smoothLocus_at_parameter Φ f hf hd i z hi v hv

end Geometry.ComplexTorus.RiemannProjectivity.ChartPeriodSmoothness.Constructions.PeriodChartSmoothness

namespace Geometry.ComplexTorus.RiemannProjectivity.ChartPeriodSmoothness.Constructions.SmoothFromComplexPoints

/-! # RiemannProjectivity: smoothness of a finite-type complex algebra is detected at its complex points -/

open OAI.Geometry.ComplexTorus.RiemannProjectivity.SmoothReferencePoint.Constructions.SmoothPointLocalization

variable {A : Type*} [CommRing A] [Algebra ℂ A]

theorem exists_character_kernel [Algebra.FiniteType ℂ A]
    (M : Ideal A) (hM : M.IsMaximal) : ∃ q : A →ₐ[ℂ] ℂ, RingHom.ker q.toRingHom = M := by
  let : M.IsMaximal := hM
  obtain ⟨n, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp
    (inferInstance : Algebra.FiniteType ℂ A)
  have hpre : (M.comap f.toRingHom).IsMaximal := Ideal.comap_isMaximal_of_surjective f.toRingHom hf
  obtain ⟨x, hx⟩ := MvPolynomial.eq_vanishingIdeal_singleton_of_isMaximal ℂ hpre
  have heval (p : MvPolynomial (Fin n) ℂ) : MvPolynomial.aeval x p = 0 ↔ f p ∈ M := by
    rw [← MvPolynomial.mem_vanishingIdeal_singleton_iff, ← hx]
    rfl
  have hker : RingHom.ker f.toRingHom ≤ RingHom.ker (MvPolynomial.aeval x).toRingHom := by
    intro p hp
    apply (heval p).mpr
    rw [show f p = 0 from hp]
    exact M.zero_mem
  let q := AlgHom.liftOfSurjective f hf (MvPolynomial.aeval x) hker
  refine ⟨q, ?_⟩
  ext a
  obtain ⟨p, rfl⟩ := hf a
  change q (f p) = 0 ↔ f p ∈ M
  rw [AlgHom.liftOfSurjective_apply]
  exact heval p

theorem smooth [Algebra.FinitePresentation ℂ A]
    (h : ∀ q : A →ₐ[ℂ] ℂ, SmoothReferencePoint.Constructions.SmoothPointLocalization.pointPrime q ∈ Algebra.smoothLocus ℂ A) : Algebra.Smooth ℂ A := by
  have hfull : Algebra.smoothLocus ℂ A = Set.univ := by
    apply Set.eq_univ_of_forall
    intro p
    obtain ⟨M, hM, hpM⟩ := Ideal.exists_le_maximal p.asIdeal p.isPrime.ne_top
    obtain ⟨q, hq⟩ := exists_character_kernel M hM
    have hle : p ≤ SmoothReferencePoint.Constructions.SmoothPointLocalization.pointPrime q := by
      change p.asIdeal ≤ RingHom.ker q.toRingHom
      rwa [hq]
    exact ((PrimeSpectrum.le_iff_specializes _ _).mp hle).mem_open
      Algebra.isOpen_smoothLocus (h q)
  exact ⟨Algebra.smoothLocus_eq_univ_iff.mp hfull, inferInstance⟩

end Geometry.ComplexTorus.RiemannProjectivity.ChartPeriodSmoothness.Constructions.SmoothFromComplexPoints

namespace Geometry.ComplexTorus.RiemannProjectivity.ChartPeriodSmoothness.Constructions.PeriodChartAlgebra

/-! # RiemannProjectivity: the entire affine chart algebra of the period image is smooth -/

open Set
open OAI.Geometry.ComplexTorus.RiemannProjectivity.ConeChartBy.Constructions.ConeChartRestriction OAI.Geometry.ComplexTorus.RiemannProjectivity.AffineVanishing.Constructions.AffineVanishingPoints OAI.Geometry.ComplexTorus.RiemannProjectivity.SmoothReferencePoint.Constructions.SmoothPointLocalization

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
  {n : ℕ}

theorem smooth (Φ : AlgebraicGeometry.ComplexMultiplication.CM.TypeHodgeStructure.CMEmbeddingType E)
    (f : Φ.periodTorus → Projectivization ℂ (Fin (n + 1) → ℂ)) (hf : Topology.IsClosedEmbedding f)
    (hd : ∀ (z : AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E) (i : Fin (n + 1)),
      f (QuotientAddGroup.mk z) ∈ (AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i).source →
      DifferentiableAt ℂ (fun w => AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i (f (QuotientAddGroup.mk w))) z ∧
      Function.Injective (fderiv ℂ (fun w => AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i (f (QuotientAddGroup.mk w))) z))
    (hS : ∀ w, (∀ p ∈ MvPolynomial.vanishingIdeal ℂ (AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.projectiveCone (range f)),
      MvPolynomial.eval w p = 0) → w ∈ AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.projectiveCone (range f)) (i : Fin (n + 1)) :
    Algebra.Smooth ℂ (AffineVanishing.Constructions.AffineVanishingPoints.coordinateRing (ConeChartBy.Constructions.ConeChartRestriction.chart (AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.projectiveCone (range f)) i)) := by
  let S := ConeChartBy.Constructions.ConeChartRestriction.chart (AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.projectiveCone (range f)) i
  let : Algebra.FinitePresentation ℂ (AffineVanishing.Constructions.AffineVanishingPoints.coordinateRing S) :=
    Algebra.FinitePresentation.quotient (IsNoetherian.noetherian _)
  apply SmoothFromComplexPoints.smooth
  intro q
  let x := AffineVanishing.Constructions.AffineVanishingPoints.coordinates S q
  have hx : x ∈ S := AffineVanishing.Constructions.AffineVanishingPoints.coordinates_mem S
    (ConeChartBy.Constructions.ConeChartRestriction.chart_determined_by_polynomials (AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.projectiveCone (range f)) hS i) q
  have hsm := PeriodChartSmoothness.mem_smoothLocus Φ f hf hd hS i x hx
  have heq : AffineCone.Constructions.AffineCoordinateSmoothness.point S x hx = q := by
    apply Ideal.Quotient.algHom_ext ℂ
    apply AlgHom.ext
    intro p
    change MvPolynomial.eval x p = q (Ideal.Quotient.mk _ p)
    exact AffineVanishing.Constructions.AffineVanishingPoints.eval_coordinates S q p
  rwa [heq] at hsm

end Geometry.ComplexTorus.RiemannProjectivity.ChartPeriodSmoothness.Constructions.PeriodChartAlgebra

end

end OAI
