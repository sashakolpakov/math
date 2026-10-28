import OAI.Geometry.ComplexTorus.RiemannProjectivity.GraphRegular
import OAI.Geometry.ComplexTorus.RiemannProjectivity.SmoothReferencePoint

/-! # Affine Cone -/

namespace OAI

noncomputable section

namespace Geometry.ComplexTorus.RiemannProjectivity.AffineCone.Constructions.AffineConeSmoothPoint

/-! # RiemannProjectivity: normalized period-cone points are smooth in their actual affine coordinate algebra -/

open Set _root_.Polynomial
open OAI.Geometry.ComplexTorus.RiemannProjectivity.ConeTangentF.Constructions.ConeTangent OAI.Geometry.ComplexTorus.RiemannProjectivity.SmoothReferencePoint.Constructions.SmoothPointLocalization OAI.Geometry.ComplexTorus.RiemannProjectivity.GraphRegular.Constructions.RegularConeNeighborhood

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
  {n : ℕ}

theorem exists_at_parameter (Φ : AlgebraicGeometry.ComplexMultiplication.CM.TypeHodgeStructure.CMEmbeddingType E)
    (f : Φ.periodTorus → Projectivization ℂ (Fin (n + 1) → ℂ)) (hf : Topology.IsClosedEmbedding f)
    (hd : ∀ (z : AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E) (i : Fin (n + 1)),
      f (QuotientAddGroup.mk z) ∈ (AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i).source →
      DifferentiableAt ℂ (fun w => AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i (f (QuotientAddGroup.mk w))) z ∧
      Function.Injective (fderiv ℂ (fun w => AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i (f (QuotientAddGroup.mk w))) z))
    (i : Fin (n + 1)) (z : AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E)
    (hi : f (QuotientAddGroup.mk z) ∈ (AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i).source)
    (v : AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.projectiveCone (range f))
    (hv : v.val = ConeTangentF.Constructions.ConeTangent.parameterization i (fun w => AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i (f (QuotientAddGroup.mk w))) (z, 1)) :
    ∃ (m : ℕ) (e : (Fin (n + 1) → ℂ) ≃L[ℂ]
        ((Fin (Module.finrank ℂ (AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E) + 1) → ℂ) × (Fin m → ℂ)))
      (q : (MvPolynomial (Fin (Module.finrank ℂ (AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E) + 1) ⊕ Fin m) ℂ ⧸
        MvPolynomial.vanishingIdeal ℂ (GraphRegular.Constructions.RegularConeNeighborhood.splitPoint e '' AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.projectiveCone (range f))) →ₐ[ℂ] ℂ),
      (∀ p, q (Ideal.Quotient.mk _ p) = MvPolynomial.eval (GraphRegular.Constructions.RegularConeNeighborhood.splitPoint e v.val) p) ∧
      SmoothReferencePoint.Constructions.SmoothPointLocalization.pointPrime q ∈ Algebra.smoothLocus ℂ
        (MvPolynomial (Fin (Module.finrank ℂ (AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E) + 1) ⊕ Fin m) ℂ ⧸
          MvPolynomial.vanishingIdeal ℂ (GraphRegular.Constructions.RegularConeNeighborhood.splitPoint e '' AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.projectiveCone (range f))) := by
  obtain ⟨m, e, F, s, q, hrel, hq, hs, hsm⟩ :=
    GraphRegular.Constructions.RegularConeNeighborhood.exists_at_parameter Φ f hf hd i z hi v hv
  let J := Ideal.span (range (fun j => JacobianLocalizationAt.Constructions.SplitPolynomialJacobian.equation j (F j)))
  let I := MvPolynomial.vanishingIdeal ℂ (GraphRegular.Constructions.RegularConeNeighborhood.splitPoint e '' AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.projectiveCone (range f))
  have hJI : J ≤ I := by
    apply Ideal.span_le.mpr
    rintro _ ⟨j, rfl⟩ _ ⟨w, hw, rfl⟩
    exact hrel w hw j
  have hk : I.map (GraphRegular.Constructions.GraphVanishingIdeal.polynomialMap F) ≤ RingHom.ker q.toRingHom := by
    apply Ideal.map_le_iff_le_comap.mpr
    intro p hp
    change q (GraphRegular.Constructions.GraphVanishingIdeal.polynomialMap F p) = 0
    rw [hq]
    exact hp (GraphRegular.Constructions.RegularConeNeighborhood.splitPoint e v.val) ⟨v.val, v.property, rfl⟩
  obtain ⟨qI, hqI, hpoint⟩ := SmoothReferencePoint.Constructions.ReferenceQuotientSmoothPoint.exists_smooth_point
    J I hJI (JacobianLocalizationAt.Constructions.SmoothEquationPoint.presentation F).jacobian q hk s hs hsm
  refine ⟨m, e, qI, ?_, hpoint⟩
  intro p
  exact (hqI p).trans (hq p)

end Geometry.ComplexTorus.RiemannProjectivity.AffineCone.Constructions.AffineConeSmoothPoint

namespace Geometry.ComplexTorus.RiemannProjectivity.AffineCone.Constructions.PolynomialCoordinates

/-! # RiemannProjectivity: linear coordinate changes act on the actual polynomial coordinate algebras -/

open scoped BigOperators

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

def linear (l : (ι → ℂ) →L[ℂ] ℂ) : MvPolynomial ι ℂ := by
  classical
  exact ∑ i : ι, MvPolynomial.C (l (Pi.single i 1)) * MvPolynomial.X i

theorem eval_linear (l : (ι → ℂ) →L[ℂ] ℂ) (x : ι → ℂ) :
    MvPolynomial.eval x (linear l) = l x := by
  classical
  have hx : (∑ i : ι, x i • Pi.single i (1 : ℂ)) = x := by
    ext j
    simp [Pi.smul_apply, Pi.single_apply]
  calc
    _ = ∑ i : ι, l (Pi.single i 1) * x i := by simp [linear]
    _ = l (∑ i : ι, x i • Pi.single i (1 : ℂ)) := by
      simp [map_sum, map_smul, smul_eq_mul, mul_comm]
    _ = l x := congrArg l hx

def substitution (L : (ι → ℂ) →L[ℂ] (κ → ℂ)) :
    MvPolynomial κ ℂ →ₐ[ℂ] MvPolynomial ι ℂ :=
  MvPolynomial.aeval (fun i => linear ((ContinuousLinearMap.proj i).comp L))

omit [Fintype κ] in
theorem eval_substitution (L : (ι → ℂ) →L[ℂ] (κ → ℂ))
    (x : ι → ℂ) (p : MvPolynomial κ ℂ) :
    MvPolynomial.eval x (substitution L p) = MvPolynomial.eval (L x) p := by
  induction p using MvPolynomial.induction_on with
  | C c => simp [substitution]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp =>
    simp only [map_mul, substitution, MvPolynomial.aeval_X, eval_linear,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply, MvPolynomial.eval_X] at *
    rw [hp]

def equiv (e : (ι → ℂ) ≃L[ℂ] (κ → ℂ)) : MvPolynomial κ ℂ ≃ₐ[ℂ] MvPolynomial ι ℂ :=
  { substitution e.toContinuousLinearMap with
    invFun := substitution e.symm.toContinuousLinearMap
    left_inv p := by
      apply MvPolynomial.funext
      intro x
      change MvPolynomial.eval x (substitution e.symm.toContinuousLinearMap
        (substitution e.toContinuousLinearMap p)) = MvPolynomial.eval x p
      rw [eval_substitution, eval_substitution]
      simp
    right_inv p := by
      apply MvPolynomial.funext
      intro x
      change MvPolynomial.eval x (substitution e.toContinuousLinearMap
        (substitution e.symm.toContinuousLinearMap p)) = MvPolynomial.eval x p
      rw [eval_substitution, eval_substitution]
      simp }

theorem equiv_eval (e : (ι → ℂ) ≃L[ℂ] (κ → ℂ)) (p : MvPolynomial κ ℂ) (x : ι → ℂ) :
    MvPolynomial.eval x (equiv e p) = MvPolynomial.eval (e x) p :=
  eval_substitution e.toContinuousLinearMap x p

end Geometry.ComplexTorus.RiemannProjectivity.AffineCone.Constructions.PolynomialCoordinates

namespace Geometry.ComplexTorus.RiemannProjectivity.AffineCone.Constructions.VanishingIdealCoordinates

/-! # RiemannProjectivity: coordinate changes preserve the actual affine vanishing-ideal quotient -/

open Set

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

theorem map_vanishingIdeal (e : (ι → ℂ) ≃L[ℂ] (κ → ℂ)) (S : Set (ι → ℂ)) :
    (MvPolynomial.vanishingIdeal ℂ (e '' S)).map (PolynomialCoordinates.equiv e).toRingHom =
      MvPolynomial.vanishingIdeal ℂ S := by
  apply le_antisymm
  · apply Ideal.map_le_iff_le_comap.mpr
    intro p hp x hx
    change MvPolynomial.eval x (PolynomialCoordinates.equiv e p) = 0
    rw [PolynomialCoordinates.equiv_eval]
    exact hp (e x) ⟨x, hx, rfl⟩
  · intro p hp
    have hpre : (PolynomialCoordinates.equiv e).symm p ∈ MvPolynomial.vanishingIdeal ℂ (e '' S) := by
      rintro _ ⟨x, hx, rfl⟩
      have heval := PolynomialCoordinates.equiv_eval e ((PolynomialCoordinates.equiv e).symm p) x
      rw [AlgEquiv.apply_symm_apply] at heval
      exact heval.symm.trans (hp x hx)
    have hm := Ideal.mem_map_of_mem (PolynomialCoordinates.equiv e).toRingHom hpre
    change (PolynomialCoordinates.equiv e) ((PolynomialCoordinates.equiv e).symm p) ∈ _ at hm
    rwa [AlgEquiv.apply_symm_apply] at hm

def equiv (e : (ι → ℂ) ≃L[ℂ] (κ → ℂ)) (S : Set (ι → ℂ)) :
    (MvPolynomial κ ℂ ⧸ MvPolynomial.vanishingIdeal ℂ (e '' S)) ≃ₐ[ℂ]
      (MvPolynomial ι ℂ ⧸ MvPolynomial.vanishingIdeal ℂ S) :=
  Ideal.quotientEquivAlg _ _ (PolynomialCoordinates.equiv e) (map_vanishingIdeal e S).symm

theorem equiv_mk (e : (ι → ℂ) ≃L[ℂ] (κ → ℂ)) (S : Set (ι → ℂ)) (p : MvPolynomial κ ℂ) :
    equiv e S (Ideal.Quotient.mk _ p) = Ideal.Quotient.mk _ (PolynomialCoordinates.equiv e p) := rfl

end Geometry.ComplexTorus.RiemannProjectivity.AffineCone.Constructions.VanishingIdealCoordinates

namespace Geometry.ComplexTorus.RiemannProjectivity.AffineCone.Constructions.AffineCoordinateSmoothness

/-! # RiemannProjectivity: smoothness at the canonical affine point is independent of linear coordinates -/

open Set
open OAI.Geometry.ComplexTorus.RiemannProjectivity.SmoothReferencePoint.Constructions.SmoothPointLocalization

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

def point (S : Set (ι → ℂ)) (x : ι → ℂ) (hx : x ∈ S) :
    (MvPolynomial ι ℂ ⧸ MvPolynomial.vanishingIdeal ℂ S) →ₐ[ℂ] ℂ :=
  Ideal.Quotient.liftₐ _ (MvPolynomial.aeval x) (fun _ hp => hp x hx)

omit [Fintype ι] in
theorem point_mk (S : Set (ι → ℂ)) (x : ι → ℂ) (hx : x ∈ S) (p : MvPolynomial ι ℂ) :
    point S x hx (Ideal.Quotient.mk _ p) = MvPolynomial.eval x p := rfl

theorem mem_smoothLocus_of_coordinates (e : (ι → ℂ) ≃L[ℂ] (κ → ℂ))
    (S : Set (ι → ℂ)) (x : ι → ℂ) (hx : x ∈ S)
    (q : (MvPolynomial κ ℂ ⧸ MvPolynomial.vanishingIdeal ℂ (e '' S)) →ₐ[ℂ] ℂ)
    (hq : ∀ p, q (Ideal.Quotient.mk _ p) = MvPolynomial.eval (e x) p)
    (hsm : SmoothReferencePoint.Constructions.SmoothPointLocalization.pointPrime q ∈ Algebra.smoothLocus ℂ
      (MvPolynomial κ ℂ ⧸ MvPolynomial.vanishingIdeal ℂ (e '' S))) :
    SmoothReferencePoint.Constructions.SmoothPointLocalization.pointPrime (point S x hx) ∈ Algebra.smoothLocus ℂ
      (MvPolynomial ι ℂ ⧸ MvPolynomial.vanishingIdeal ℂ S) := by
  let a := VanishingIdealCoordinates.equiv e S
  apply SmoothReferencePoint.Constructions.SmoothPointLocalization.mem_smoothLocus_of_equiv a (point S x hx)
  have heq : (point S x hx).comp a.toAlgHom = q := by
    apply Ideal.Quotient.algHom_ext ℂ
    apply AlgHom.ext
    intro p
    change point S x hx (VanishingIdealCoordinates.equiv e S (Ideal.Quotient.mk _ p)) =
      q (Ideal.Quotient.mk _ p)
    rw [VanishingIdealCoordinates.equiv_mk, point_mk, PolynomialCoordinates.equiv_eval, hq]
  rwa [heq]

end Geometry.ComplexTorus.RiemannProjectivity.AffineCone.Constructions.AffineCoordinateSmoothness

namespace Geometry.ComplexTorus.RiemannProjectivity.AffineCone.Constructions.NormalizedConeSmoothness

/-! # RiemannProjectivity: the canonical normalized CM cone point is an algebraically smooth point -/

open Set
open OAI.Geometry.ComplexTorus.RiemannProjectivity.ConeTangentF.Constructions.ConeTangent OAI.Geometry.ComplexTorus.RiemannProjectivity.SmoothReferencePoint.Constructions.SmoothPointLocalization

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
  {n : ℕ}

theorem mem_smoothLocus_at_parameter (Φ : AlgebraicGeometry.ComplexMultiplication.CM.TypeHodgeStructure.CMEmbeddingType E)
    (f : Φ.periodTorus → Projectivization ℂ (Fin (n + 1) → ℂ)) (hf : Topology.IsClosedEmbedding f)
    (hd : ∀ (z : AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E) (i : Fin (n + 1)),
      f (QuotientAddGroup.mk z) ∈ (AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i).source →
      DifferentiableAt ℂ (fun w => AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i (f (QuotientAddGroup.mk w))) z ∧
      Function.Injective (fderiv ℂ (fun w => AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i (f (QuotientAddGroup.mk w))) z))
    (i : Fin (n + 1)) (z : AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E)
    (hi : f (QuotientAddGroup.mk z) ∈ (AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i).source)
    (v : AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.projectiveCone (range f))
    (hv : v.val = ConeTangentF.Constructions.ConeTangent.parameterization i (fun w => AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i (f (QuotientAddGroup.mk w))) (z, 1)) :
    SmoothReferencePoint.Constructions.SmoothPointLocalization.pointPrime (AffineCoordinateSmoothness.point (AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.projectiveCone (range f)) v.val v.property) ∈
      Algebra.smoothLocus ℂ
        (MvPolynomial (Fin (n + 1)) ℂ ⧸ MvPolynomial.vanishingIdeal ℂ (AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.projectiveCone (range f))) := by
  obtain ⟨m, e, q, hq, hsm⟩ := AffineConeSmoothPoint.exists_at_parameter Φ f hf hd i z hi v hv
  let a := e.trans (LinearEquiv.sumArrowLequivProdArrow
    (Fin (Module.finrank ℂ (AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E) + 1)) (Fin m) ℂ ℂ).symm.toContinuousLinearEquiv
  exact AffineCoordinateSmoothness.mem_smoothLocus_of_coordinates a
    (AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.projectiveCone (range f)) v.val v.property q hq hsm

end Geometry.ComplexTorus.RiemannProjectivity.AffineCone.Constructions.NormalizedConeSmoothness

namespace Geometry.ComplexTorus.RiemannProjectivity.AffineCone.Constructions.SmoothRetract

/-! # RiemannProjectivity: smoothness descends to an algebra retract -/

variable {R A B : Type*} [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B]

theorem formallySmooth [Algebra.FormallySmooth R B]
    (i : A →ₐ[R] B) (r : B →ₐ[R] A) (h : r.comp i = AlgHom.id R A) :
    Algebra.FormallySmooth R A := by
  apply Algebra.FormallySmooth.of_comp_surjective
  intro C _ _ I hI f
  obtain ⟨g, hg⟩ := Algebra.FormallySmooth.comp_surjective R B I hI (f.comp r)
  refine ⟨g.comp i, ?_⟩
  rw [← AlgHom.comp_assoc, hg, AlgHom.comp_assoc, h, AlgHom.comp_id]

theorem smooth [Algebra.Smooth R B] [Algebra.FinitePresentation R A]
    (i : A →ₐ[R] B) (r : B →ₐ[R] A) (h : r.comp i = AlgHom.id R A) :
    Algebra.Smooth R A :=
  ⟨formallySmooth i r h, inferInstance⟩

end Geometry.ComplexTorus.RiemannProjectivity.AffineCone.Constructions.SmoothRetract

namespace Geometry.ComplexTorus.RiemannProjectivity.AffineCone.Constructions.PointStalkMaps

/-! # RiemannProjectivity: algebra maps induce compatible maps of the genuine point local rings -/

open OAI.Geometry.ComplexTorus.RiemannProjectivity.SmoothReferencePoint.Constructions.SmoothPointLocalization

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra ℂ A] [Algebra ℂ B]

abbrev stalk (q : A →ₐ[ℂ] ℂ) := Localization.AtPrime (SmoothReferencePoint.Constructions.SmoothPointLocalization.pointPrime q).asIdeal

theorem primeCompl_le (f : A →ₐ[ℂ] B) (qA : A →ₐ[ℂ] ℂ) (qB : B →ₐ[ℂ] ℂ)
    (h : qB.comp f = qA) :
    (SmoothReferencePoint.Constructions.SmoothPointLocalization.pointPrime qA).asIdeal.primeCompl ≤
      (SmoothReferencePoint.Constructions.SmoothPointLocalization.pointPrime qB).asIdeal.primeCompl.comap f.toRingHom := by
  intro a ha
  change qB (f a) ≠ 0
  have heq : qB (f a) = qA a := congrArg (fun q : A →ₐ[ℂ] ℂ => q a) h
  rw [heq]
  exact ha

def map (f : A →ₐ[ℂ] B) (qA : A →ₐ[ℂ] ℂ) (qB : B →ₐ[ℂ] ℂ)
    (h : qB.comp f = qA) : stalk qA →ₐ[ℂ] stalk qB :=
  { IsLocalization.map (stalk qB) f.toRingHom (primeCompl_le f qA qB h) with
    commutes' c := by
      rw [IsScalarTower.algebraMap_apply ℂ A (stalk qA)]
      change IsLocalization.map (stalk qB) f.toRingHom (primeCompl_le f qA qB h)
        (algebraMap A (stalk qA) (algebraMap ℂ A c)) = algebraMap ℂ (stalk qB) c
      rw [IsLocalization.map_eq]
      change algebraMap B (stalk qB) (f (algebraMap ℂ A c)) = algebraMap ℂ (stalk qB) c
      rw [f.commutes, ← IsScalarTower.algebraMap_apply ℂ B (stalk qB)] }

theorem map_algebraMap (f : A →ₐ[ℂ] B) (qA : A →ₐ[ℂ] ℂ) (qB : B →ₐ[ℂ] ℂ)
    (h : qB.comp f = qA) (a : A) :
    PointStalkMaps.map f qA qB h (algebraMap A (stalk qA) a) = algebraMap B (stalk qB) (f a) := by
  exact IsLocalization.map_eq (primeCompl_le f qA qB h) a

theorem smooth_retract_at_point (i : A →ₐ[ℂ] B) (r : B →ₐ[ℂ] A)
    (h : r.comp i = AlgHom.id ℂ A) (qA : A →ₐ[ℂ] ℂ)
    (hsm : SmoothReferencePoint.Constructions.SmoothPointLocalization.pointPrime (qA.comp r) ∈ Algebra.smoothLocus ℂ B) :
    SmoothReferencePoint.Constructions.SmoothPointLocalization.pointPrime qA ∈ Algebra.smoothLocus ℂ A := by
  let qB := qA.comp r
  have hi : qB.comp i = qA := by
    change (qA.comp r).comp i = qA
    rw [AlgHom.comp_assoc, h, AlgHom.comp_id]
  let fi := PointStalkMaps.map i qA qB hi
  let fr := PointStalkMaps.map r qB qA rfl
  have hfi : fr.comp fi = AlgHom.id ℂ (stalk qA) := by
    apply IsLocalization.algHom_ext (SmoothReferencePoint.Constructions.SmoothPointLocalization.pointPrime qA).asIdeal.primeCompl
    ext a
    change fr (fi (algebraMap A (stalk qA) a)) = algebraMap A (stalk qA) a
    rw [map_algebraMap, map_algebraMap]
    exact congrArg (algebraMap A (stalk qA)) (congrArg (fun f : A →ₐ[ℂ] A => f a) h)
  let : Algebra.FormallySmooth ℂ (stalk qB) := hsm
  exact SmoothRetract.formallySmooth fi fr hfi

end Geometry.ComplexTorus.RiemannProjectivity.AffineCone.Constructions.PointStalkMaps

end

end OAI
