import OAI.Geometry.ComplexTorus.RiemannProjectivity.PolynomialFiber
import OAI.Geometry.ComplexTorus.RiemannProjectivity.ConstantFiber
import OAI.Geometry.ComplexTorus.RiemannProjectivity.AnalyticCone
import OAI.Geometry.ComplexTorus.RiemannProjectivity.ConeSurjectivityEq

/-! # Global Equation -/

namespace OAI

noncomputable section

namespace Geometry.ComplexTorus.RiemannProjectivity.GlobalEquation.Constructions.GlobalMonicEquation

/-!
# RiemannProjectivity: a monic algebraic equation over the entire affine base

The canonical family has constant degree on the punctured complex base.
Its lower coefficients extend as multivariable polynomials. Fixing the
leading coefficient to one produces one actual polynomial over the base
polynomial ring, with the exact fibers away from the vertex.
-/

open Set Filter _root_.Polynomial
open scoped _root_.Topology
open scoped BigOperators

def GenericallySeparable {d : ℕ} (F : Polynomial (MvPolynomial (Fin (d + 1)) ℂ)) : Prop :=
  ∀ x : Fin (d + 1) → ℂ, x ≠ 0 → ∃ᶠ y in 𝓝 x, (F.map (MvPolynomial.eval y)).Separable

theorem exists_equation {d : ℕ} {S : Set ((Fin (d + 1) → ℂ) × ℂ)}
    (hproper : IsProperMap (fun p : S => p.val.1))
    (hfinite : ∀ x, {z : ℂ | (x, z) ∈ S}.Finite)
    (hlocal : ∀ x, x ≠ 0 → ∀ z, (x, z) ∈ S →
      PeriodWhole.Constructions.PeriodCoordinateEquations.HasLocalMonicEquation S x z)
    {C : ℝ} (hroot : ∀ x, x ≠ 0 → ∀ z, (x, z) ∈ S → ‖z‖ ≤ C * ‖x‖) :
    ∃ (k : ℕ) (F : Polynomial (MvPolynomial (Fin (d + 1)) ℂ)),
      (∀ y, (F.map (MvPolynomial.eval y)).Monic ∧
        (F.map (MvPolynomial.eval y)).natDegree = k) ∧
      GenericallySeparable F ∧ ∀ x, x ≠ 0 → ∀ z, (x, z) ∈ S ↔ F.eval₂ (MvPolynomial.eval x) z = 0 := by
  have hloc : ∀ x ∈ ({x | x ≠ 0} : Set (Fin (d + 1) → ℂ)),
      ∃ (U : Set (Fin (d + 1) → ℂ)) (P : (Fin (d + 1) → ℂ) → ℂ[X]),
        IsOpen U ∧ x ∈ U ∧ U ⊆ {x | x ≠ 0} ∧ ReducedFamiliesOn.Constructions.ReducedFamilies.On S U P := by
    intro x hx
    obtain ⟨U, P, hU, hxU, hP⟩ :=
      ReducedFamiliesOn.Constructions.ReducedFamilies.exists_local hproper (hfinite x) (hlocal x hx)
    exact ⟨U ∩ {x | x ≠ 0}, P, hU.inter isOpen_compl_singleton, ⟨hxU, hx⟩,
      inter_subset_right, hP.mono inter_subset_left⟩
  obtain ⟨Q, hQc, hQm, hQr, hQlocal⟩ := GlueReduced.Constructions.GlueReducedFamilies.exists_global hloc
  obtain ⟨k, hk⟩ := ConstantFiber.Constructions.ConstantFiberDegree.exists_constant_degree hQlocal
  have hQroot (x : Fin (d + 1) → ℂ) (hx : x ≠ 0) (z : ℂ) (hz : (Q x).eval z = 0) :
      ‖z‖ ≤ C * ‖x‖ := hroot x hx z ((hQr x hx z).mpr hz)
  have hb := fun j => ReducedFamiliesOn.Constructions.ReducedDegree.coefficient_growth hQm (fun x hx => (hk x hx).le) hQroot j
  have hpoly (j : ℕ) : ∃ A : MvPolynomial (Fin (d + 1)) ℂ,
      ∀ x, x ≠ 0 → MvPolynomial.eval x A = (Q x).coeff j := by
    obtain ⟨A, hA, _⟩ := PolynomialExtensionOf.Constructions.PolynomialExtension.exists_polynomial_of_punctured_growth
      (fun x hx => (hQc j).differentiableAt (isOpen_compl_singleton.mem_nhds hx)) (hb j)
    exact ⟨A, hA⟩
  choose A hA using hpoly
  let F : Polynomial (MvPolynomial (Fin (d + 1)) ℂ) :=
    X ^ k + ∑ j ∈ Finset.range k, monomial j (A j)
  have hmap (y : Fin (d + 1) → ℂ) : F.map (MvPolynomial.eval y) =
      CoefficientRoot.Constructions.MonicFamily.ofCoefficients k (fun j => MvPolynomial.eval y (A j)) := by
    simp only [F, CoefficientRoot.Constructions.MonicFamily.ofCoefficients, Polynomial.map_add, Polynomial.map_pow,
      Polynomial.map_X, Polynomial.map_sum, Polynomial.map_monomial]
  have heq (y : Fin (d + 1) → ℂ) (hy : y ≠ 0) : F.map (MvPolynomial.eval y) = Q y := by
    rw [hmap]
    exact CoefficientRoot.Constructions.MonicFamily.ofCoefficients_eq (hQm y hy) (hk y hy) (fun j _ => hA j y hy)
  have hgen : GenericallySeparable F := by
    intro x hx
    obtain ⟨U, hU, hxU, hUB, hOn⟩ := hQlocal x hx
    obtain ⟨c, _, hn, hs⟩ := hOn.generic
    exact ((not_eventually.mp (hn x hxU)).and_eventually (hU.mem_nhds hxU)).mono
      (fun y hy => by rw [heq y (hUB hy.2)]; exact hs y hy.2 hy.1)
  refine ⟨k, F, fun y => ?_, hgen, ?_⟩
  · rw [hmap]
    exact CoefficientRoot.Constructions.MonicFamily.monic_ofCoefficients k _
  · intro x hx z
    rw [← eval_map, heq x hx]
    exact hQr x hx z

end Geometry.ComplexTorus.RiemannProjectivity.GlobalEquation.Constructions.GlobalMonicEquation

namespace Geometry.ComplexTorus.RiemannProjectivity.GlobalEquation.Constructions.VertexEquation

/-! # RiemannProjectivity: the global polynomial has exactly the cone vertex over zero -/

open Set _root_.Polynomial

theorem root_at_zero {d k : ℕ} (F : Polynomial (MvPolynomial (Fin (d + 1)) ℂ))
    (hF : ∀ y, (F.map (MvPolynomial.eval y)).Monic ∧
      (F.map (MvPolynomial.eval y)).natDegree = k)
    {C : ℝ} (hbound : ∀ y : Fin (d + 1) → ℂ, y ≠ 0 → ∀ z,
      F.eval₂ (MvPolynomial.eval y) z = 0 → ‖z‖ ≤ C * ‖y‖)
    {z : ℂ} (hz : F.eval₂ (MvPolynomial.eval (0 : Fin (d + 1) → ℂ)) z = 0) : z = 0 := by
  let Q : (Fin (d + 1) → ℂ) → ℂ[X] := fun y => F.map (MvPolynomial.eval y)
  have hc (j : ℕ) : ContinuousAt (fun y => (Q y).coeff j) (0 : Fin (d + 1) → ℂ) := by
    simpa only [Q, coeff_map] using (F.coeff j).continuous_eval.continuousAt
  have hclosed : IsClosed {p : (Fin (d + 1) → ℂ) × ℂ | ‖p.2‖ ≤ C * ‖p.1‖} :=
    isClosed_le continuous_snd.norm (continuous_const.mul continuous_fst.norm)
  have hnorm := RootContinuityAt.Constructions.RootClosure.root_mem_closed hclosed k hF
    ((dense_compl_singleton (0 : Fin (d + 1) → ℂ)) 0) hc
    (fun y hy w hw => hbound y hy w (by simpa only [Q, eval_map] using hw))
    (by simpa only [Q, eval_map] using hz)
  change ‖z‖ ≤ C * ‖(0 : Fin (d + 1) → ℂ)‖ at hnorm
  simp only [norm_zero, mul_zero] at hnorm
  exact norm_eq_zero.mp (le_antisymm hnorm (norm_nonneg z))

theorem exists_exact_equation {d : ℕ} {S : Set ((Fin (d + 1) → ℂ) × ℂ)}
    (hproper : IsProperMap (fun p : S => p.val.1))
    (hfinite : ∀ x, {z : ℂ | (x, z) ∈ S}.Finite)
    (hlocal : ∀ x, x ≠ 0 → ∀ z, (x, z) ∈ S →
      PeriodWhole.Constructions.PeriodCoordinateEquations.HasLocalMonicEquation S x z)
    {C : ℝ} (hroot : ∀ x, x ≠ 0 → ∀ z, (x, z) ∈ S → ‖z‖ ≤ C * ‖x‖)
    (hvertex : ∀ z, ((0 : Fin (d + 1) → ℂ), z) ∈ S ↔ z = 0)
    (hne : ∃ (x : Fin (d + 1) → ℂ), x ≠ 0 ∧ ∃ z, (x, z) ∈ S) :
    ∃ (k : ℕ) (F : Polynomial (MvPolynomial (Fin (d + 1)) ℂ)),
      0 < k ∧ (∀ y, (F.map (MvPolynomial.eval y)).Monic ∧
        (F.map (MvPolynomial.eval y)).natDegree = k) ∧
      GlobalMonicEquation.GenericallySeparable F ∧ ∀ x z, (x, z) ∈ S ↔ F.eval₂ (MvPolynomial.eval x) z = 0 := by
  obtain ⟨k, F, hF, hgen, heq⟩ := GlobalMonicEquation.exists_equation hproper hfinite hlocal hroot
  have hk : k ≠ 0 := by
    intro hk0
    obtain ⟨x, hx, z, hz⟩ := hne
    have hone : F.map (MvPolynomial.eval x) = 1 :=
      (hF x).1.natDegree_eq_zero.mp (by rw [(hF x).2, hk0])
    have hzero := (heq x hx z).mp hz
    rw [← eval_map, hone, eval_one] at hzero
    exact one_ne_zero hzero
  have hbound : ∀ y : Fin (d + 1) → ℂ, y ≠ 0 → ∀ z,
      F.eval₂ (MvPolynomial.eval y) z = 0 → ‖z‖ ≤ C * ‖y‖ :=
    fun y hy z hz => hroot y hy z ((heq y hy z).mpr hz)
  have hz0 : F.eval₂ (MvPolynomial.eval (0 : Fin (d + 1) → ℂ)) 0 = 0 := by
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_root (F.map (MvPolynomial.eval (0 : Fin (d + 1) → ℂ)))
      (fun hdeg => hk ((hF 0).2.symm.trans (natDegree_eq_of_degree_eq_some hdeg)))
    have heval : F.eval₂ (MvPolynomial.eval (0 : Fin (d + 1) → ℂ)) z = 0 := by
      simpa only [IsRoot, eval_map] using hz
    have hzero := root_at_zero F hF hbound heval
    rwa [hzero] at heval
  refine ⟨k, F, Nat.pos_of_ne_zero hk, hF, hgen, ?_⟩
  intro x z
  by_cases hx : x = 0
  · subst x
    rw [hvertex]
    exact ⟨fun hz => hz ▸ hz0, root_at_zero F hF hbound⟩
  · exact heq x hx z

end Geometry.ComplexTorus.RiemannProjectivity.GlobalEquation.Constructions.VertexEquation

namespace Geometry.ComplexTorus.RiemannProjectivity.GlobalEquation.Constructions.PeriodAlgebraicCoordinates

/-! # RiemannProjectivity: polynomial equations for actual coordinate images of the CM cone -/

open Set _root_.Polynomial

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
  {n : ℕ}

theorem coordinate_equation (Φ : AlgebraicGeometry.ComplexMultiplication.CM.TypeHodgeStructure.CMEmbeddingType E)
    (f : Φ.periodTorus → Projectivization ℂ (Fin (n + 1) → ℂ)) (hf : Topology.IsClosedEmbedding f)
    (hd : ∀ (z : AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E) (i : Fin (n + 1)),
      f (QuotientAddGroup.mk z) ∈ (AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i).source →
      DifferentiableAt ℂ (fun w => AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i (f (QuotientAddGroup.mk w))) z ∧
      Function.Injective (fderiv ℂ (fun w => AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i (f (QuotientAddGroup.mk w))) z))
    (L : (Fin (n + 1) → ℂ) →L[ℂ] (Fin (Module.finrank ℂ (AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E) + 1) → ℂ))
    (hker : ∀ v ∈ AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.projectiveCone (range f), L v = 0 → v = 0)
    (hsurj : Function.Surjective (fun v : AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.projectiveCone (range f) => L v))
    (l : (Fin (n + 1) → ℂ) →L[ℂ] ℂ) (hl : Function.Surjective (L.prod l)) :
    ∃ (k : ℕ) (F : Polynomial (MvPolynomial (Fin (Module.finrank ℂ (AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E) + 1)) ℂ)),
      0 < k ∧ (∀ y, (F.map (MvPolynomial.eval y)).Monic ∧
        (F.map (MvPolynomial.eval y)).natDegree = k) ∧
      GlobalMonicEquation.GenericallySeparable F ∧ ∀ x z, (x, z) ∈ (fun v => (L v, l v)) '' AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.projectiveCone (range f) ↔
        F.eval₂ (MvPolynomial.eval x) z = 0 := by
  let T := AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.projectiveCone (range f)
  let S := (fun v => (L v, l v)) '' T
  have hT : IsClosed T := AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.isClosed_projectiveCone (range f) hf.isClosed_range
  have hTc := AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.smul_mem_projectiveCone (range f)
  have hTa := FiniteCone.Constructions.FiniteConeFibers.cone_holomorphic_of_period_embedding Φ f hf hd
  have hLp := AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.Projection.Constructions.Cone.isProperMap_projection hT hTc L hker
  have hLf := FiniteCone.Constructions.FiniteConeFibers.finite_proper_cone_fiber L hLp hker hTa
  have hpairker : ∀ v ∈ T, (L.prod l) v = 0 → v = 0 :=
    fun v hv hzero => hker v hv (congrArg Prod.fst hzero)
  have hp := AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.Projection.Constructions.Cone.isProperMap_projection hT hTc (L.prod l) hpairker
  have hS : IsClosed S := by
    have h := hp.isClosedMap.isClosed_range
    convert! h using 1
    ext u
    exact ⟨fun ⟨v, hv, he⟩ => ⟨⟨v, hv⟩, he⟩,
      fun ⟨v, he⟩ => ⟨v, v.property, he⟩⟩
  have hSc : ∀ (a : ℂ) ⦃p⦄, p ∈ S → a • p ∈ S := by
    rintro a p ⟨v, hv, rfl⟩
    exact ⟨a • v, hTc a hv, by simp only [map_smul]; rfl⟩
  have hSker : ∀ p ∈ S, p.1 = 0 → p = 0 := by
    rintro p ⟨v, hv, rfl⟩ hzero
    change (L v, l v) = 0
    rw [hker v hv hzero]
    simp only [map_zero, Prod.zero_eq_mk]
  have hSproper := AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.Projection.Constructions.Cone.isProperMap_projection hS hSc
    (ContinuousLinearMap.fst ℂ (Fin (Module.finrank ℂ (AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E) + 1) → ℂ) ℂ) hSker
  have hSfinite (x : Fin (Module.finrank ℂ (AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E) + 1) → ℂ) :
      {z : ℂ | (x, z) ∈ S}.Finite := by
    apply ((hLf x).image l).subset
    rintro z ⟨v, hv, heq⟩
    exact ⟨v, ⟨hv, congrArg Prod.fst heq⟩, congrArg Prod.snd heq⟩
  have hSloc (x : Fin (Module.finrank ℂ (AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E) + 1) → ℂ) (hx : x ≠ 0)
      (z : ℂ) (hz : (x, z) ∈ S) : PeriodWhole.Constructions.PeriodCoordinateEquations.HasLocalMonicEquation S x z := by
    have ha := AnalyticCone.Constructions.AnalyticConeImage.linear_projection (L.prod l) hl hT hTc hpairker hTa
      (x, z) hz (fun hzero => hx (congrArg Prod.fst hzero))
    exact ConePolynomial.Constructions.ConePolynomialEquations.local_equation_of_coordinate_image Φ f hf.isEmbedding
      (fun z i hi => (hd z i hi).1) L hLf l hS hx ha
  obtain ⟨C, _, hbound⟩ := AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.Projection.Constructions.Cone.norm_le_projection hS hSc
    (ContinuousLinearMap.fst ℂ (Fin (Module.finrank ℂ (AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E) + 1) → ℂ) ℂ) hSker
  have hroot (x : Fin (Module.finrank ℂ (AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E) + 1) → ℂ) (_ : x ≠ 0)
      (z : ℂ) (hz : (x, z) ∈ S) : ‖z‖ ≤ C * ‖x‖ :=
    (norm_snd_le (x, z)).trans (hbound (x, z) hz)
  have hvertex : ∀ z, ((0 : Fin (Module.finrank ℂ (AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E) + 1) → ℂ), z) ∈ S ↔ z = 0 := by
    intro z
    constructor
    · intro hz
      exact congrArg Prod.snd (hSker (0, z) hz rfl)
    · intro hz
      subst z
      exact ⟨0, AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.zero_mem_projectiveCone _, by simp only [map_zero]⟩
  have hne : ∃ (x : Fin (Module.finrank ℂ (AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E) + 1) → ℂ),
      x ≠ 0 ∧ ∃ z, (x, z) ∈ S := by
    obtain ⟨v, hv⟩ := hsurj (fun _ => 1)
    refine ⟨fun _ => 1, fun h => one_ne_zero (congrFun h 0), l v, v, v.property, ?_⟩
    exact Prod.ext hv rfl
  exact VertexEquation.exists_exact_equation hSproper hSfinite hSloc hroot hvertex hne

end Geometry.ComplexTorus.RiemannProjectivity.GlobalEquation.Constructions.PeriodAlgebraicCoordinates

namespace Geometry.ComplexTorus.RiemannProjectivity.GlobalEquation.Constructions.LinearPolynomial

/-! # RiemannProjectivity: polynomial pullback along linear coordinates -/

open _root_.Polynomial
open scoped BigOperators

variable {n m : ℕ}

def linear (l : (Fin n → ℂ) →L[ℂ] ℂ) : MvPolynomial (Fin n) ℂ :=
  ∑ i : Fin n, MvPolynomial.C (l (Pi.single i 1)) * MvPolynomial.X i

theorem eval_linear (l : (Fin n → ℂ) →L[ℂ] ℂ) (x : Fin n → ℂ) :
    MvPolynomial.eval x (linear l) = l x := by
  have hx : (∑ i : Fin n, x i • Pi.single i (1 : ℂ)) = x := by
    ext j
    simp [Pi.smul_apply, Pi.single_apply]
  calc
    _ = ∑ i : Fin n, l (Pi.single i 1) * x i := by simp [linear]
    _ = l (∑ i : Fin n, x i • Pi.single i (1 : ℂ)) := by
      simp [map_sum, map_smul, smul_eq_mul, mul_comm]
    _ = l x := congrArg l hx

def substitution (L : (Fin n → ℂ) →L[ℂ] (Fin m → ℂ)) :
    MvPolynomial (Fin m) ℂ →+* MvPolynomial (Fin n) ℂ :=
  MvPolynomial.eval₂Hom MvPolynomial.C
    (fun i => linear ((ContinuousLinearMap.proj i).comp L))

theorem eval_substitution (L : (Fin n → ℂ) →L[ℂ] (Fin m → ℂ))
    (x : Fin n → ℂ) (p : MvPolynomial (Fin m) ℂ) :
    MvPolynomial.eval x (substitution L p) = MvPolynomial.eval (L x) p := by
  change MvPolynomial.eval x (MvPolynomial.eval₂ MvPolynomial.C
    (fun i => linear ((ContinuousLinearMap.proj i).comp L)) p) = _
  rw [MvPolynomial.eval_eval₂]
  have hC : (MvPolynomial.eval x).comp MvPolynomial.C = RingHom.id ℂ := by ext a; simp
  simp only [hC, eval_linear, ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply]
  rfl

def pullback (L : (Fin n → ℂ) →L[ℂ] (Fin m → ℂ)) (l : (Fin n → ℂ) →L[ℂ] ℂ)
    (F : Polynomial (MvPolynomial (Fin m) ℂ)) : MvPolynomial (Fin n) ℂ :=
  F.eval₂ (substitution L) (linear l)

theorem eval_pullback (L : (Fin n → ℂ) →L[ℂ] (Fin m → ℂ)) (l : (Fin n → ℂ) →L[ℂ] ℂ)
    (F : Polynomial (MvPolynomial (Fin m) ℂ)) (x : Fin n → ℂ) :
    MvPolynomial.eval x (pullback L l F) = F.eval₂ (MvPolynomial.eval (L x)) (l x) := by
  change MvPolynomial.eval x (F.eval₂ (substitution L) (linear l)) = _
  induction F using Polynomial.induction_on' with
  | add P Q ihP ihQ => simp only [eval₂_add, map_add, ihP, ihQ]
  | monomial k a =>
    simp only [eval₂_monomial, map_mul, map_pow, eval_substitution, eval_linear]

end Geometry.ComplexTorus.RiemannProjectivity.GlobalEquation.Constructions.LinearPolynomial

end

end OAI
