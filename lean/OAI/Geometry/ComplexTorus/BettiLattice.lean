import Mathlib
import OAI.AlgebraicGeometry.ComplexMultiplication.WeightOne
import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Topology.Algebra.Group.Quotient

/-! # Betti Lattice -/

namespace OAI.Geometry.ComplexTorus.BettiLattice.CM.Construction

noncomputable section

/-! BettiLattice: complex tori as lattice quotients and rational H¹ as the lattice dual.
The comparison with singular cohomology is a separate result. -/

open scoped TensorProduct

-- Proposed general complex-torus interface.
structure Torus where
  V : Type
  [normedGroup : NormedAddCommGroup V]
  [complexSpace : NormedSpace ℂ V]
  [finiteDimensional : FiniteDimensional ℂ V]
  [rationalModule : Module ℚ V]
  [rationalTower : IsScalarTower ℚ ℂ V]
  lattice : Submodule ℤ V
  [discrete : DiscreteTopology lattice]
  [full : IsZLattice ℝ lattice]

attribute [instance]
  Torus.normedGroup Torus.complexSpace Torus.finiteDimensional
  Torus.rationalModule Torus.rationalTower Torus.discrete Torus.full

abbrev Torus.Point (A : Torus) :=
  A.V ⧸ A.lattice.toAddSubgroup

abbrev Torus.LQ (A : Torus) :=
  Submodule.span ℚ (A.lattice : Set A.V)

abbrev Torus.H1Q (A : Torus) :=
  Module.Dual ℚ A.LQ

def Torus.proj (A : Torus) : A.V → A.Point :=
  QuotientAddGroup.mk

-- Local holomorphic lifts express holomorphicity for the quotient
-- complex structure, without requiring a global linear lift.
def Holomorphic {A B : Torus} (g : A.Point →+ B.Point) : Prop :=
  ∀ v : A.V, ∃ (s : Set A.V) (F : A.V → B.V),
    IsOpen s ∧ v ∈ s ∧ DifferentiableOn ℂ F s ∧
      ∀ w ∈ s, g (A.proj w) = B.proj (F w)

def PreservesLattice {A B : Torus} (f : A.V →ₗ[ℂ] B.V) : Prop :=
  ∀ v ∈ A.lattice, f v ∈ B.lattice

def Lifts {A B : Torus}
    (g : A.Point →+ B.Point) (f : A.V →ₗ[ℂ] B.V) : Prop :=
  ∀ v, g (A.proj v) = B.proj (f v)

-- Explicit identification of the lattice-dual Hodge structure:
-- complexification evaluates canonically on rational lattice vectors;
-- its (1,0)-part consists of restrictions of complex-linear covectors.
structure H1Model (A : Torus) where
  hodge : AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure A.H1Q
  comparison :
    AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.Complexification A.H1Q ≃ₗ[ℂ] (A.LQ →ₗ[ℚ] ℂ)
  comparison_tmul :
    ∀ (z : ℂ) (φ : A.H1Q) (v : A.LQ),
      comparison (z ⊗ₜ[ℚ] φ) v = z * (φ v : ℂ)
  holomorphic_iff :
    ∀ x, x ∈ hodge.holomorphic ↔
      ∃ ℓ : A.V →ₗ[ℂ] ℂ,
        ∀ v : A.LQ, comparison x v = ℓ (v : A.V)

open _root_.Topology Filter

@[simp] theorem Torus.proj_zero (A : Torus) : A.proj 0 = 0 := rfl
@[simp] theorem Torus.proj_add (A : Torus) (x y : A.V) :
    A.proj (x + y) = A.proj x + A.proj y := rfl
@[simp] theorem Torus.proj_sub (A : Torus) (x y : A.V) :
    A.proj (x - y) = A.proj x - A.proj y := rfl
@[simp] theorem Torus.proj_eq_zero (A : Torus) (v : A.V) :
    A.proj v = 0 ↔ v ∈ A.lattice := QuotientAddGroup.eq_zero_iff v

theorem Torus.covering (A : Torus) : IsCoveringMap A.proj :=
  (A.lattice.toAddSubgroup.isAddQuotientCoveringMap_of_comm
    (SetLike.isDiscrete_iff_discreteTopology.mpr A.discrete)).isCoveringMap

theorem Holomorphic.continuous_comp {A B : Torus} {g : A.Point →+ B.Point}
    (hg : Holomorphic g) : Continuous (fun v => g (A.proj v)) := by
  rw [continuous_iff_continuousAt]
  intro v
  obtain ⟨s, F, hs, hv, hF, he⟩ := hg v
  have hd := (hF v hv).differentiableAt (hs.mem_nhds hv)
  apply (B.covering.continuous.continuousAt.comp hd.continuousAt).congr
  filter_upwards [hs.mem_nhds hv] with w hw
  exact (he w hw).symm

/-- Local lifts and a continuous global lift agree locally after translation. -/
theorem Holomorphic.differentiable_lift_zero {A B : Torus} {g : A.Point →+ B.Point}
    (hg : Holomorphic g) (F : C(A.V, B.V)) (hF0 : F 0 = 0)
    (hF : ∀ v, B.proj (F v) = g (A.proj v)) : DifferentiableAt ℂ F 0 := by
  obtain ⟨s, G, hs, h0, hG, hGq⟩ := hg 0
  have hd := (hG 0 h0).differentiableAt (hs.mem_nhds h0)
  have hq0 : B.proj (G 0) = 0 := by simpa using (hGq 0 h0).symm
  obtain ⟨t, ht, ht0, hinj⟩ := B.covering.isLocalHomeomorph.isLocallyInjective 0
  have hFt : ∀ᶠ x in 𝓝 (0 : A.V), F x ∈ t :=
    F.continuous.continuousAt.eventually (by simpa [hF0] using ht.mem_nhds ht0)
  have hGt : ∀ᶠ x in 𝓝 (0 : A.V), G x - G 0 ∈ t :=
    (hd.continuousAt.sub_const (G 0)).eventually (by simpa using ht.mem_nhds ht0)
  have he : F =ᶠ[𝓝 (0 : A.V)] (fun x => G x - G 0) := by
    filter_upwards [hs.mem_nhds h0, hFt, hGt] with x hx hxF hxG
    apply hinj hxF hxG
    rw [Torus.proj_sub, hq0, sub_zero, hF x, hGq x hx]
  exact (hd.sub_const (G 0)).congr_of_eventuallyEq he

/-- A holomorphic quotient homomorphism has a unique complex-linear lift. -/
theorem holomorphic_linear_lift (A B : Torus) (g : A.Point →+ B.Point)
    (hg : Holomorphic g) :
    ∃! f : A.V →ₗ[ℂ] B.V, PreservesLattice f ∧ Lifts g f := by
  let qg : C(A.V, B.Point) := ⟨fun v => g (A.proj v), hg.continuous_comp⟩
  obtain ⟨F, ⟨hF0, hF⟩, _⟩ := B.covering.existsUnique_continuousMap_lifts
    qg 0 0 (by simp [qg])
  have hlift (v : A.V) : B.proj (F v) = g (A.proj v) := congrFun hF v
  have hadd (x y : A.V) : F (x + y) = F x + F y := by
    have he : (fun p : A.V × A.V => F (p.1 + p.2)) =
        (fun p : A.V × A.V => F p.1 + F p.2) :=
      B.covering.eq_of_comp_eq
        (F.continuous.comp (continuous_fst.add continuous_snd))
        ((F.continuous.comp continuous_fst).add (F.continuous.comp continuous_snd))
        (by ext p; simp [hlift]) (0, 0) (by simp [hF0])
    exact congrFun he (x, y)
  let fR : A.V →L[ℝ] B.V :=
    (show A.V →+ B.V from ⟨⟨F, hF0⟩, hadd⟩).toRealLinearMap F.continuous
  have hd := hg.differentiable_lift_zero F hF0 hlift
  let f := (fderiv ℂ F 0).toLinearMap
  have hlin : ∀ v, f v = F v := by
    have he := (hd.hasFDerivAt.restrictScalars ℝ).unique (fR.hasFDerivAt (x := 0))
    intro v
    exact congrArg (fun h : A.V →L[ℝ] B.V => h v) he
  refine ⟨f, ⟨?_, ?_⟩, ?_⟩
  · intro v hv
    rw [← B.proj_eq_zero, hlin, hlift, (A.proj_eq_zero v).mpr hv, map_zero]
  · intro v
    rw [hlin, hlift]
  · intro f' hf'
    apply LinearMap.ext
    have he : (fun v => f' v) = (fun v => f v) := B.covering.eq_of_comp_eq
      f'.continuous_of_finiteDimensional f.continuous_of_finiteDimensional
      (by ext v; exact (hf'.2 v).symm.trans (by change g (A.proj v) = B.proj (f v); rw [hlin, hlift]))
      0 (by simp)
    exact congrFun he

/-- A lattice-preserving linear map descends to the quotient. -/
def descend {A B : Torus} (f : A.V →ₗ[ℂ] B.V) (hf : PreservesLattice f) :
    A.Point →+ B.Point :=
  QuotientAddGroup.lift A.lattice.toAddSubgroup
    ((QuotientAddGroup.mk' B.lattice.toAddSubgroup).comp f.toAddMonoidHom)
    (fun v hv => (B.proj_eq_zero (f v)).mpr (hf v hv))

theorem descend_lifts {A B : Torus} (f : A.V →ₗ[ℂ] B.V) (hf : PreservesLattice f) :
    Lifts (descend f hf) f := fun _ => rfl

theorem descend_holomorphic {A B : Torus} (f : A.V →ₗ[ℂ] B.V)
    (hf : PreservesLattice f) : Holomorphic (descend f hf) := by
  intro v
  exact ⟨Set.univ, f, isOpen_univ, Set.mem_univ v,
    f.toContinuousLinearMap.differentiable.differentiableOn, fun _ _ => rfl⟩

theorem lifts_group_unique {A B : Torus} {g g' : A.Point →+ B.Point}
    {f : A.V →ₗ[ℂ] B.V} (hg : Lifts g f) (hg' : Lifts g' f) : g = g' := by
  ext v
  exact (hg v).trans (hg' v).symm

theorem lattice_description (A B : Torus) :
    (∀ g : A.Point →+ B.Point, Holomorphic g →
      ∃! f : A.V →ₗ[ℂ] B.V, PreservesLattice f ∧ Lifts g f) ∧
    (∀ f : A.V →ₗ[ℂ] B.V, PreservesLattice f →
      ∃! g : A.Point →+ B.Point, Holomorphic g ∧ Lifts g f) := by
  refine ⟨holomorphic_linear_lift A B, ?_⟩
  intro f hf
  exact ⟨descend f hf, ⟨descend_holomorphic f hf, descend_lifts f hf⟩,
    fun g hg => lifts_group_unique hg.2 (descend_lifts f hf)⟩

theorem Torus.complex_span (A : Torus) :
    Submodule.span ℂ (A.lattice : Set A.V) = ⊤ :=
  Submodule.span_eq_top_of_span_eq_top ℝ ℂ _ A.full.span_top

theorem linear_ext_lq {A B : Torus} {f g : A.V →ₗ[ℂ] B.V}
    (h : ∀ v : A.LQ, f v = g v) : f = g := by
  apply LinearMap.ext_on A.complex_span
  intro v hv
  exact h ⟨v, Submodule.subset_span hv⟩

def restrictCovector (A : Torus) :
    Module.Dual ℂ A.V →ₗ[ℂ] (A.LQ →ₗ[ℚ] ℂ) where
  toFun ℓ := (ℓ.restrictScalars ℚ).comp A.LQ.subtype
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem restrictCovector_apply (A : Torus) (ℓ : Module.Dual ℂ A.V) (v : A.LQ) :
    restrictCovector A ℓ v = ℓ (v : A.V) := rfl

theorem restrictCovector_injective (A : Torus) : Function.Injective (restrictCovector A) := by
  intro f g h
  apply LinearMap.ext_on A.complex_span
  intro v hv
  exact LinearMap.congr_fun h ⟨v, Submodule.subset_span hv⟩

/-- Complex covectors identify with the prescribed holomorphic subspace. -/
def covectorEquiv {A : Torus} (HA : H1Model A) :
    Module.Dual ℂ A.V ≃ₗ[ℂ] HA.hodge.holomorphic :=
  LinearEquiv.ofBijective
    (((HA.comparison.symm.toLinearMap).comp (restrictCovector A)).codRestrict
      HA.hodge.holomorphic (fun ℓ => (HA.holomorphic_iff _).mpr
        ⟨ℓ, fun v => by simp⟩)) (by
    constructor
    · intro f g h
      apply restrictCovector_injective A
      have he := congrArg (fun x : HA.hodge.holomorphic => HA.comparison x) h
      simpa using he
    · intro x
      obtain ⟨ℓ, hℓ⟩ := (HA.holomorphic_iff x).mp x.property
      refine ⟨ℓ, Subtype.ext (HA.comparison.injective ?_)⟩
      ext v
      simpa using (hℓ v).symm)

@[simp] theorem comparison_covectorEquiv {A : Torus} (HA : H1Model A)
    (ℓ : Module.Dual ℂ A.V) (v : A.LQ) :
    HA.comparison (covectorEquiv HA ℓ) v = ℓ (v : A.V) := by
  change HA.comparison (HA.comparison.symm (restrictCovector A ℓ)) v = _
  simp

@[simp] theorem covectorEquiv_symm_apply {A : Torus} (HA : H1Model A)
    (x : HA.hodge.holomorphic) (v : A.LQ) :
    (covectorEquiv HA).symm x (v : A.V) = HA.comparison x v := by
  rw [← comparison_covectorEquiv HA ((covectorEquiv HA).symm x),
    LinearEquiv.apply_symm_apply]

theorem H1Model.finite_lq {A : Torus} (HA : H1Model A) : FiniteDimensional ℚ A.LQ :=
  (Module.finite_dual_iff ℚ).mp HA.hodge.finiteDimensional

/-- Transposition on finite-dimensional vector spaces, using the canonical bidual maps. -/
def transpose {K X Y : Type*} [Field K] [AddCommGroup X] [Module K X]
    [AddCommGroup Y] [Module K Y] [FiniteDimensional K X] [FiniteDimensional K Y]
    (u : Module.Dual K Y →ₗ[K] Module.Dual K X) : X →ₗ[K] Y :=
  (Module.evalEquiv K Y).symm.toLinearMap.comp
    (u.dualMap.comp (Module.evalEquiv K X).toLinearMap)

@[simp] theorem transpose_apply {K X Y : Type*} [Field K] [AddCommGroup X] [Module K X]
    [AddCommGroup Y] [Module K Y] [FiniteDimensional K X] [FiniteDimensional K Y]
    (u : Module.Dual K Y →ₗ[K] Module.Dual K X) (ℓ : Module.Dual K Y) (x : X) :
    ℓ (transpose u x) = u ℓ x := by
  simp [transpose, LinearMap.dualMap_apply']

def hodgeCovectorMap {A B : Torus} (HA : H1Model A) (HB : H1Model B)
    (u : B.H1Q →ₗ[ℚ] A.H1Q) (hu : AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.IsHodgeMap HB.hodge HA.hodge u) :
    Module.Dual ℂ B.V →ₗ[ℂ] Module.Dual ℂ A.V :=
  (covectorEquiv HA).symm.toLinearMap.comp
    ((((u.baseChange ℂ).comp HB.hodge.holomorphic.subtype).codRestrict
      HA.hodge.holomorphic (fun x => hu x x.property)).comp
        (covectorEquiv HB).toLinearMap)

theorem comparison_baseChange {A B : Torus} (HA : H1Model A) (HB : H1Model B)
    (u : B.H1Q →ₗ[ℚ] A.H1Q) (fQ : A.LQ →ₗ[ℚ] B.LQ)
    (he : ∀ (φ : B.H1Q) (v : A.LQ), φ (fQ v) = u φ v)
    (x : AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.Complexification B.H1Q) (v : A.LQ) :
    HA.comparison (u.baseChange ℂ x) v = HB.comparison x (fQ v) := by
  induction x using TensorProduct.inductionOn with
  | tmul z φ => simp [HA.comparison_tmul, HB.comparison_tmul, he]
  | add x y hx hy => simp [hx, hy]

/-- A Hodge map determines a complex-linear map compatible with its rational transpose. -/
theorem hodge_linear_map {A B : Torus} (HA : H1Model A) (HB : H1Model B)
    (u : B.H1Q →ₗ[ℚ] A.H1Q) (hu : AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.IsHodgeMap HB.hodge HA.hodge u) :
    ∃ (f : A.V →ₗ[ℂ] B.V) (fQ : A.LQ →ₗ[ℚ] B.LQ),
      (∀ v : A.LQ, (fQ v : B.V) = f (v : A.V)) ∧
      (∀ φ : B.H1Q, φ.comp fQ = u φ) := by
  have := HA.finite_lq
  have := HB.finite_lq
  let fQ := transpose u
  let f := transpose (hodgeCovectorMap HA HB u hu)
  refine ⟨f, fQ, ?_, ?_⟩
  · intro v
    apply (Module.evalEquiv ℂ B.V).injective
    apply LinearMap.ext
    intro ℓ
    change ℓ (fQ v : B.V) = ℓ (f (v : A.V))
    rw [transpose_apply]
    change ℓ (fQ v : B.V) = (covectorEquiv HA).symm _ (v : A.V)
    rw [covectorEquiv_symm_apply]
    exact (comparison_baseChange HA HB u fQ (transpose_apply u)
      (covectorEquiv HB ℓ) v).trans (comparison_covectorEquiv HB ℓ (fQ v)) |>.symm
  · intro φ
    ext v
    exact transpose_apply u φ v

/-- Each rational lattice vector has an integral positive multiple in the lattice. -/
theorem denominator_mem (A : Torus) {v : A.V} (hv : v ∈ A.LQ) :
    ∃ n : ℕ, 0 < n ∧ n • v ∈ A.lattice := by
  induction hv using Submodule.span_induction with
  | mem x hx => exact ⟨1, Nat.zero_lt_one, by simpa using hx⟩
  | zero => exact ⟨1, Nat.zero_lt_one, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨n, hn, hx⟩ := hx
    obtain ⟨m, hm, hy⟩ := hy
    refine ⟨n * m, Nat.mul_pos hn hm, ?_⟩
    have hx' := A.lattice.toAddSubgroup.nsmul_mem hx m
    have hy' := A.lattice.toAddSubgroup.nsmul_mem hy n
    simpa [nsmul_add, ← mul_nsmul, mul_comm] using A.lattice.add_mem hx' hy'
  | smul q x _ hx =>
    obtain ⟨n, hn, hx⟩ := hx
    refine ⟨n * q.den, Nat.mul_pos hn q.den_pos, ?_⟩
    have he : (n * q.den) • (q • x) = q.num • (n • x) := by
      simp only [← Nat.cast_smul_eq_nsmul ℚ, ← Int.cast_smul_eq_zsmul ℚ,
        smul_smul, Nat.cast_mul]
      congr 1
      rw [mul_assoc, Rat.den_mul_eq_num, mul_comm]
    rw [he]
    exact A.lattice.smul_mem q.num hx

/-- A finite list of rational lattice vectors has a common positive denominator. -/
theorem finite_denominator {ι : Type*} (s : Finset ι) (B : Torus) (v : ι → B.V)
    (hv : ∀ i ∈ s, v i ∈ B.LQ) :
    ∃ n : ℕ, 0 < n ∧ ∀ i ∈ s, n • v i ∈ B.lattice := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨1, Nat.zero_lt_one, by simp⟩
  | @insert i s hi ih =>
    obtain ⟨n, hn, hni⟩ := denominator_mem B (hv i (Finset.mem_insert_self _ _))
    obtain ⟨m, hm, hms⟩ := ih (fun j hj => hv j (Finset.mem_insert_of_mem hj))
    refine ⟨n * m, Nat.mul_pos hn hm, ?_⟩
    intro j hj
    rcases Finset.mem_insert.mp hj with rfl | hj
    · simpa [← mul_nsmul, mul_comm] using B.lattice.toAddSubgroup.nsmul_mem hni m
    · simpa [← mul_nsmul, mul_comm] using B.lattice.toAddSubgroup.nsmul_mem (hms j hj) n

/-- Clear denominators uniformly on the finitely generated source lattice. -/
theorem clear_denominators {A B : Torus} (f : A.V →ₗ[ℂ] B.V)
    (hf : ∀ v ∈ A.lattice, f v ∈ B.LQ) :
    ∃ n : ℕ, 0 < n ∧ PreservesLattice ((n : ℂ) • f) := by
  obtain ⟨s, hs⟩ := ZLattice.FG ℝ A.lattice
  obtain ⟨n, hn, hns⟩ := finite_denominator s B f (fun v hv =>
    hf v (by rw [← hs]; exact Submodule.subset_span hv))
  refine ⟨n, hn, ?_⟩
  intro v hv
  have hall : ∀ v ∈ Submodule.span ℤ (s : Set A.V), n • f v ∈ B.lattice := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx => exact hns x hx
    | zero => simp
    | add x y _ _ hx hy => simpa [map_add, nsmul_add] using B.lattice.add_mem hx hy
    | smul z x _ hx =>
      simpa [map_zsmul, smul_comm z n] using B.lattice.smul_mem z hx
  simpa only [LinearMap.smul_apply, Nat.cast_smul_eq_nsmul] using hall v (hs.symm ▸ hv)

/-- A complex-linear map on vector spaces induces a Hodge map on the lattice duals. -/
theorem pullback_isHodgeMap {A B : Torus} (HA : H1Model A) (HB : H1Model B)
    (f : A.V →ₗ[ℂ] B.V) (fQ : A.LQ →ₗ[ℚ] B.LQ)
    (hf : ∀ v : A.LQ, (fQ v : B.V) = f (v : A.V)) :
    AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.IsHodgeMap HB.hodge HA.hodge fQ.dualMap := by
  intro x hx
  obtain ⟨ℓ, hℓ⟩ := (HB.holomorphic_iff x).mp hx
  apply (HA.holomorphic_iff _).mpr
  refine ⟨ℓ.comp f, ?_⟩
  intro v
  rw [comparison_baseChange HA HB fQ.dualMap fQ (fun _ _ => rfl), hℓ, hf]
  rfl

theorem isHodgeMap_smul_iff {A B : Torus} (HA : H1Model A) (HB : H1Model B)
    (u : B.H1Q →ₗ[ℚ] A.H1Q) (q : ℚ) (hq : q ≠ 0) :
    AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.IsHodgeMap HB.hodge HA.hodge (q • u) ↔ AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.IsHodgeMap HB.hodge HA.hodge u := by
  constructor
  · intro hu x hx
    have h := HA.hodge.holomorphic.smul_mem (q : ℂ)⁻¹ (hu x hx)
    simpa [LinearMap.baseChange_smul, ← Rat.cast_smul_eq_qsmul ℂ,
      smul_smul, hq] using h
  · intro hu x hx
    simpa [LinearMap.baseChange_smul, ← Rat.cast_smul_eq_qsmul ℂ] using
      HA.hodge.holomorphic.smul_mem (q : ℂ) (hu x hx)

/-- Contravariant rational correspondence, expressed by clearing denominators. -/
theorem rational_hodge_description
    (A B : Torus) (HA : H1Model A) (HB : H1Model B)
    (u : B.H1Q →ₗ[ℚ] A.H1Q) :
    AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.IsHodgeMap HB.hodge HA.hodge u ↔
      ∃ n : ℕ, 0 < n ∧
        ∃! g : A.Point →+ B.Point,
          Holomorphic g ∧
          ∃ (f : A.V →ₗ[ℂ] B.V) (fQ : A.LQ →ₗ[ℚ] B.LQ),
            PreservesLattice f ∧
            Lifts g f ∧
            (∀ v : A.LQ, (fQ v : B.V) = f (v : A.V)) ∧
            (∀ φ : B.H1Q, φ.comp fQ = (n : ℚ) • (u φ)) := by
  have := HB.finite_lq
  constructor
  · intro hu
    obtain ⟨f, fQ, hcompat, hpull⟩ := hodge_linear_map HA HB u hu
    obtain ⟨n, hn, hnf⟩ := clear_denominators f (fun v hv => by
      let vQ : A.LQ := ⟨v, Submodule.subset_span hv⟩
      exact hcompat vQ ▸ (fQ vQ).property)
    let fn : A.V →ₗ[ℂ] B.V := (n : ℂ) • f
    let fnQ : A.LQ →ₗ[ℚ] B.LQ := (n : ℚ) • fQ
    have hncompat (v : A.LQ) : (fnQ v : B.V) = fn (v : A.V) := by
      change (n : ℚ) • (fQ v : B.V) = (n : ℂ) • f (v : A.V)
      rw [hcompat]
      simp only [Nat.cast_smul_eq_nsmul]
    have hnpull (φ : B.H1Q) : φ.comp fnQ = (n : ℚ) • (u φ) := by
      ext v
      change φ ((n : ℚ) • fQ v) = (n : ℚ) • u φ v
      rw [map_smul]
      exact congrArg (fun x : ℚ => (n : ℚ) • x) (LinearMap.congr_fun (hpull φ) v)
    refine ⟨n, hn, descend fn hnf,
      ⟨descend_holomorphic fn hnf, fn, fnQ, hnf, descend_lifts fn hnf, hncompat, hnpull⟩,
      ?_⟩
    rintro g' ⟨_, f', fQ', _, hlift', hcompat', hpull'⟩
    have hQQ : fQ' = fnQ := by
      apply LinearMap.ext
      intro v
      apply (Module.evalEquiv ℚ B.LQ).injective
      apply LinearMap.ext
      intro φ
      exact (LinearMap.congr_fun (hpull' φ) v).trans
        (LinearMap.congr_fun (hnpull φ) v).symm
    have hff : f' = fn := linear_ext_lq (fun v =>
      (hcompat' v).symm.trans ((congrArg (fun h : A.LQ →ₗ[ℚ] B.LQ => (h v : B.V)) hQQ).trans
        (hncompat v)))
    exact lifts_group_unique (hff ▸ hlift') (descend_lifts fn hnf)
  · rintro ⟨n, hn, g, ⟨_, f, fQ, _, _, hcompat, hpull⟩, _⟩
    have he : fQ.dualMap = (n : ℚ) • u := by
      apply LinearMap.ext
      intro φ
      exact hpull φ
    apply (isHodgeMap_smul_iff HA HB u (n : ℚ) (by exact_mod_cast hn.ne')).mp
    rw [← he]
    exact pullback_isHodgeMap HA HB f fQ hcompat

end

end OAI.Geometry.ComplexTorus.BettiLattice.CM.Construction
