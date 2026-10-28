import OAI.AlgebraicGeometry.PELModuli.CMPoints.CountableSubmersionFiber
import Mathlib.Data.Set.Finite.Lemmas
import OAI.Geometry.ComplexTorus.RiemannProjectivity.FiniteBranchesAt

/-! # Countable Holomorphic Image -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.PELModuli.CMPoints.CountableHolomorphicImage.CountableMaximalRank

/-!
# CMPoints: a countable holomorphic fiber at maximal rank is regular

Project to the derivative's image and use its implicit-function coordinates.
The countable-fiber chart theorem removes every vertical direction, forcing the
original derivative to be injective.
-/

open Set Filter _root_.Module
open scoped _root_.Topology ContDiff

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
  [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℂ W]

theorem injective_fderiv_of_maximal_rank {F : V → W} {U : Set V}
    (hU : IsOpen U) (hF : DifferentiableOn ℂ F U) {x : V} (hx : x ∈ U)
    (hmax : ∀ z ∈ U, finrank ℂ (fderiv ℂ F z).range ≤ finrank ℂ (fderiv ℂ F x).range)
    (hcountable : {z : V | z ∈ U ∧ F z = F x}.Countable) : Function.Injective (fderiv ℂ F x) := by
  let : CompleteSpace V := FiniteDimensional.complete ℂ V
  let A := fderiv ℂ F x
  let R := A.range
  obtain ⟨Q₀, hQ₀⟩ := R.subtype.exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr Subtype.val_injective)
  let Q := Q₀.toContinuousLinearMap
  have hQ (v : R) : Q v = v := LinearMap.congr_fun hQ₀ v
  let d := Q.comp A
  have hd : Function.Surjective d := by
    intro y
    obtain ⟨v, hv⟩ := y.property
    change A v = (y : W) at hv
    exact ⟨v, by change Q (A v) = y; rw [hv]; exact hQ y⟩
  let G : V → R := fun z => Q (F z)
  have hGder : HasFDerivAt G d x :=
    Q.hasFDerivAt.comp x (hF.differentiableAt (hU.mem_nhds hx)).hasFDerivAt
  let : Subsingleton d.ker := CountableSubmersionFiber.subsingleton_kernel_of_countable_fiber
    hU hF hx Q d hGder hd hmax hcountable
  have hd0 : ∀ v, d v = 0 → v = 0 := by
    intro v hv
    exact congrArg Subtype.val (Subsingleton.elim (⟨v, hv⟩ : d.ker) 0)
  have hdinj : Function.Injective d := (injective_iff_map_eq_zero d).mpr hd0
  intro v w hvw
  exact hdinj (congrArg Q hvw)

theorem exists_injective_point {F : V → W} {U : Set V}
    (hU : IsOpen U) (hne : U.Nonempty) (hF : DifferentiableOn ℂ F U)
    (hcountable : ∀ y, {z : V | z ∈ U ∧ F z = y}.Countable) :
    ∃ x ∈ U, Function.Injective (fderiv ℂ F x) := by
  let r : V → ℕ := fun x => finrank ℂ (fderiv ℂ F x).range
  have hr : (r '' U).Finite := by
    apply (Finset.range (finrank ℂ V + 1)).finite_toSet.subset
    rintro _ ⟨z, _, rfl⟩
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (fderiv ℂ F z).toLinearMap.finrank_range_le)
  obtain ⟨m, hm, hmax⟩ := Set.exists_max_image (r '' U) id hr (hne.image r)
  obtain ⟨x, hx, hxm⟩ := hm
  refine ⟨x, hx, injective_fderiv_of_maximal_rank hU hF hx ?_ (hcountable (F x))⟩
  intro z hz
  have h := hmax (r z) ⟨z, hz, rfl⟩
  change r z ≤ m at h
  rw [← hxm] at h
  exact h

theorem dense_injective_points {F : V → W} {U : Set V}
    (hU : IsOpen U) (hF : DifferentiableOn ℂ F U)
    (hcountable : ∀ y, {z : V | z ∈ U ∧ F z = y}.Countable) :
    U ⊆ closure {x | x ∈ U ∧ Function.Injective (fderiv ℂ F x)} := by
  intro x hx
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  obtain ⟨z, hz, hi⟩ := exists_injective_point (hU.inter Metric.isOpen_ball)
    ⟨x, hx, Metric.mem_ball_self hε⟩ (hF.mono inter_subset_left)
    (fun y => (hcountable y).mono (show
      {z : V | z ∈ U ∩ Metric.ball x ε ∧ F z = y} ⊆
        {z : V | z ∈ U ∧ F z = y} from fun _ hz => ⟨hz.1.1, hz.2⟩))
  exact ⟨z, ⟨hz.1, hi⟩, by simpa only [Metric.mem_ball, dist_comm] using hz.2⟩

end AlgebraicGeometry.PELModuli.CMPoints.CountableHolomorphicImage.CountableMaximalRank

namespace AlgebraicGeometry.PELModuli.CMPoints.CountableHolomorphicImage

/-! A holomorphic map with countable fibers between spaces of equal
complex dimension has a nonempty open subset of its image. -/

open Set _root_.Module
open scoped _root_.Topology

variable {V W : Type*}
  [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
  [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℂ W]

theorem exists_open_subset_image_of_countable_fibers
    {f : V → W} {U : Set V} (hU : IsOpen U) (hne : U.Nonempty)
    (hf : DifferentiableOn ℂ f U)
    (hdim : finrank ℂ V = finrank ℂ W)
    (hcountable : ∀ y, {x : V | x ∈ U ∧ f x = y}.Countable) :
    ∃ O : Set W, IsOpen O ∧ O.Nonempty ∧ O ⊆ f '' U := by
  obtain ⟨x, hx, hi⟩ := CountableMaximalRank.exists_injective_point hU hne hf hcountable
  have hs : Function.Surjective (fderiv ℂ f x) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hi
  obtain ⟨e, hxe, hef, _⟩ :=
    Geometry.ComplexTorus.RiemannProjectivity.FiniteBranchesAt.Constructions.FiniteBranches.holomorphic_local_inverse hU hf hx ⟨hi, hs⟩
  let d := e.restrOpen U hU
  have hxd : x ∈ d.source := ⟨hxe, hx⟩
  refine ⟨d.target, d.open_target, ⟨d x, d.map_source hxd⟩, ?_⟩
  intro y hy
  have hinv := d.map_target hy
  refine ⟨d.symm y, hinv.2, ?_⟩
  have heq : (d : V → W) = f := hef
  rw [← heq]
  exact d.right_inv hy

end AlgebraicGeometry.PELModuli.CMPoints.CountableHolomorphicImage

end

end OAI
