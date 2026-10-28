import OAI.Geometry.ComplexTorus.RiemannProjectivity.LocalReduced
import OAI.Geometry.ComplexTorus.RiemannProjectivity.PeriodWhole
import OAI.Geometry.ComplexTorus.RiemannProjectivity.RemovableGlobal
import OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.MonicRoots
import OAI.Geometry.ComplexTorus.RiemannProjectivity.CoefficientRoot

/-! # Reduced Families On -/

namespace OAI

noncomputable section

namespace Geometry.ComplexTorus.RiemannProjectivity.ReducedFamiliesOn.Constructions.ReducedFamilies

/-! # RiemannProjectivity: canonical reduced polynomial families and uniqueness on overlaps -/

open Set Filter _root_.Polynomial
open scoped _root_.Topology

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

structure On (S : Set (V × ℂ)) (U : Set V) (P : V → ℂ[X]) : Prop where
  holomorphic : ∀ j, DifferentiableOn ℂ (fun y => (P y).coeff j) U
  monic : ∀ y ∈ U, (P y).Monic
  constant_degree : ∃ k, ∀ y ∈ U, (P y).natDegree = k
  roots : ∀ y ∈ U, ∀ z, (y, z) ∈ S ↔ (P y).eval z = 0
  generic : ∃ c : V → ℂ, DifferentiableOn ℂ c U ∧
    (∀ x ∈ U, ¬∀ᶠ y in 𝓝 x, c y = 0) ∧
    ∀ y ∈ U, c y ≠ 0 → (P y).Separable

theorem On.mono {S : Set (V × ℂ)} {U W : Set V} {P : V → ℂ[X]}
    (hP : On S U P) (hWU : W ⊆ U) : On S W P := by
  obtain ⟨k, hk⟩ := hP.constant_degree
  obtain ⟨c, hc, hn, hs⟩ := hP.generic
  exact ⟨fun j => (hP.holomorphic j).mono hWU, fun y hy => hP.monic y (hWU hy),
    ⟨k, fun y hy => hk y (hWU hy)⟩, fun y hy => hP.roots y (hWU hy),
    c, hc.mono hWU, fun y hy => hn y (hWU hy), fun y hy => hs y (hWU hy)⟩

theorem eq_at {S : Set (V × ℂ)} {U W : Set V} {P Q : V → ℂ[X]}
    (hU : IsOpen U) (hW : IsOpen W) (hP : On S U P) (hQ : On S W Q)
    {x : V} (hxU : x ∈ U) (hxW : x ∈ W) : P x = Q x := by
  obtain ⟨c, hc, hcn, hPs⟩ := hP.generic
  obtain ⟨d, hd, hdn, hQs⟩ := hQ.generic
  have hn := AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.GenericDegree.Constructions.GenericPolynomial.not_eventually_zero_mul (hU.inter hW) ⟨hxU, hxW⟩
    (hc.mono inter_subset_left) (hd.mono inter_subset_right) (hcn x hxU) (hdn x hxW)
  ext j
  apply RemovableGlobal.Constructions.GlobalRemovability.eq_at_of_nonflat hn
    (((hP.holomorphic j).differentiableAt (hU.mem_nhds hxU)).continuousAt)
    (((hQ.holomorphic j).differentiableAt (hW.mem_nhds hxW)).continuousAt)
  filter_upwards [hU.mem_nhds hxU, hW.mem_nhds hxW] with y hyU hyW hycd
  have hcd : c y ≠ 0 ∧ d y ≠ 0 := mul_ne_zero_iff.mp hycd
  have heq := AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.MonicRoots.Constructions.RootPolynomials.eq_of_same_roots (hP.monic y hyU) (hQ.monic y hyW)
    (hPs y hyU hcd.1) (hQs y hyW hcd.2)
    (fun z => (hP.roots y hyU z).symm.trans (hQ.roots y hyW z))
  exact congrArg (fun p : ℂ[X] => p.coeff j) heq

theorem exists_local {d : ℕ} {S : Set ((Fin d → ℂ) × ℂ)} {x : Fin d → ℂ}
    (hproper : IsProperMap (fun p : S => p.val.1))
    (hfinite : {z : ℂ | (x, z) ∈ S}.Finite)
    (hlocal : ∀ z, (x, z) ∈ S → PeriodWhole.Constructions.PeriodCoordinateEquations.HasLocalMonicEquation S x z) :
    ∃ (U : Set (Fin d → ℂ)) (P : (Fin d → ℂ) → ℂ[X]),
      IsOpen U ∧ x ∈ U ∧ On S U P := by
  obtain ⟨k, O, P, hO, hxO, hPc, hP, hProots⟩ :=
    PeriodWhole.Constructions.WholeFiberPolynomial.exists_polynomial hproper hfinite hlocal
  obtain ⟨m, Q, U, c, hU, hxU, hUO, hc, hdense, hQc, hQ, hQs, hroots⟩ :=
    LocalReduced.Constructions.LocalReducedFamily.exists_reduced_family hO hPc k hP hxO
  refine ⟨U, Q, hU, hxU, ⟨hQc, fun y _ => (hQ y).1,
    ⟨m, fun y _ => (hQ y).2⟩, fun y hy z => (hProots y (hUO hy) z).trans (hroots y hy z),
    c, hc, ?_, hQs⟩⟩
  intro y hy hz
  obtain ⟨w, hw, hwzero⟩ := ((mem_closure_iff_frequently.mp (hdense hy)).and_eventually hz).exists
  exact hw.2 hwzero

end Geometry.ComplexTorus.RiemannProjectivity.ReducedFamiliesOn.Constructions.ReducedFamilies

namespace Geometry.ComplexTorus.RiemannProjectivity.ReducedFamiliesOn.Constructions.ReducedDegree

/-! # RiemannProjectivity: uniform degree and coefficient bounds for reduced families -/

open Set Filter _root_.Polynomial
open scoped _root_.Topology
open OAI.Geometry.ComplexTorus.RiemannProjectivity.ReducedFamiliesOn.Constructions.ReducedFamilies

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

theorem natDegree_le {S : Set (V × ℂ)} {U : Set V} {P : V → ℂ[X]}
    (hU : IsOpen U) (hP : ReducedFamilies.On S U P) {N : ℕ}
    (hcard : ∀ y ∈ U, {z : ℂ | (y, z) ∈ S}.ncard ≤ N)
    {x : V} (hx : x ∈ U) : (P x).natDegree ≤ N := by
  obtain ⟨k, hk⟩ := hP.constant_degree
  obtain ⟨c, _, hn, hs⟩ := hP.generic
  have hf : ∃ᶠ y in 𝓝 x, c y ≠ 0 := by
    simpa only [Filter.Frequently, not_not] using hn x hx
  obtain ⟨y, hcy, hy⟩ := (hf.and_eventually (hU.mem_nhds hx)).exists
  have hset : {z : ℂ | (y, z) ∈ S} = {z : ℂ | (P y).eval z = 0} :=
    Set.ext (fun z => hP.roots y hy z)
  have heq : {z : ℂ | (y, z) ∈ S}.ncard = (P y).natDegree := by
    rw [hset]
    exact AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.MonicRoots.Constructions.RootPolynomials.ncard_zero_set (hP.monic y hy).ne_zero (hs y hy hcy)
  rw [hk x hx, ← hk y hy, ← heq]
  exact hcard y hy

omit [NormedSpace ℂ V] in
theorem coefficient_growth {P : V → ℂ[X]} {U : Set V} {N : ℕ} {C : ℝ}
    (hmonic : ∀ x ∈ U, (P x).Monic) (hdegree : ∀ x ∈ U, (P x).natDegree ≤ N)
    (hroot : ∀ x ∈ U, ∀ z, (P x).eval z = 0 → ‖z‖ ≤ C * ‖x‖) (j : ℕ) :
    ∀ x ∈ U, ‖(P x).coeff j‖ ≤
      ((N.choose j : ℝ) * (max 1 C) ^ N) * (max 1 ‖x‖) ^ N := by
  intro x hx
  have hchoose : ((P x).natDegree.choose j : ℝ) ≤ (N.choose j : ℝ) := by
    exact_mod_cast Nat.choose_le_choose j (hdegree x hx)
  have hmax : max 1 (C * ‖x‖) ≤ max 1 C * max 1 ‖x‖ := by
    apply max_le
    · exact one_le_mul_of_one_le_of_one_le (le_max_left _ _) (le_max_left _ _)
    · exact mul_le_mul (le_max_right _ _) (le_max_right _ _) (norm_nonneg x)
        (zero_le_one.trans (le_max_left _ _))
  calc
    _ ≤ ((P x).natDegree.choose j : ℝ) * (max 1 (C * ‖x‖)) ^ (P x).natDegree :=
      CoefficientRoot.Constructions.RootCoefficientBound.norm_coeff_le (hmonic x hx) (hroot x hx) j
    _ ≤ (N.choose j : ℝ) * (max 1 (C * ‖x‖)) ^ N :=
      mul_le_mul hchoose (pow_le_pow_right₀ (le_max_left _ _) (hdegree x hx))
        (pow_nonneg (zero_le_one.trans (le_max_left _ _)) _) (Nat.cast_nonneg _)
    _ ≤ (N.choose j : ℝ) * (max 1 C * max 1 ‖x‖) ^ N := by gcongr
    _ = _ := by rw [mul_pow, mul_assoc]

end Geometry.ComplexTorus.RiemannProjectivity.ReducedFamiliesOn.Constructions.ReducedDegree

end

end OAI
