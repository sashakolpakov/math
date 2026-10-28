import OAI.Geometry.ComplexTorus.RiemannProjectivity.GlobalEquation
import Mathlib.Algebra.Module.Submodule.Union
import OAI.Geometry.ComplexTorus.RiemannProjectivity.AnalyticCone

/-! # Separating Linear Coordinates -/

namespace OAI

noncomputable section

namespace Geometry.ComplexTorus.RiemannProjectivity.SeparatingLinearCoordinates.Constructions.LinearSeparation

/-! # RiemannProjectivity: a linear coordinate separates a point from a finite projection fiber -/

open Set

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [NormedAddCommGroup W] [NormedSpace ℂ W]

theorem surjective_prod (L : V →L[ℂ] W) (hL : Function.Surjective L) (l : V →L[ℂ] ℂ)
    {v : V} (hv : L v = 0) (hlv : l v ≠ 0) : Function.Surjective (L.prod l) := by
  rintro ⟨x, z⟩
  obtain ⟨w, hw⟩ := hL x
  refine ⟨w + ((z - l w) / l v) • v, Prod.ext ?_ ?_⟩
  · change L (w + ((z - l w) / l v) • v) = x
    simp only [map_add, map_smul, hv, smul_zero, add_zero, hw]
  · change l (w + ((z - l w) / l v) • v) = z
    simp only [map_add, map_smul, smul_eq_mul, div_mul_cancel₀ _ hlv]
    ring

variable [FiniteDimensional ℂ V]

theorem exists_coordinate (L : V →L[ℂ] W) {S : Set V}
    (hsurj : Function.Surjective (fun v : S => L v))
    (hfinite : ∀ y, {w : V | w ∈ S ∧ L w = y}.Finite)
    {v : V} (hv : v ∉ S) :
    ∃ l : V →L[ℂ] ℂ, Function.Surjective (L.prod l) ∧
      ∀ w ∈ S, L w = L v → l w ≠ l v := by
  classical
  let K := {w : V | w ∈ S ∧ L w = L v}
  let : Fintype K := (hfinite (L v)).fintype
  have hn (w : K) : v - w.val ≠ 0 := by
    intro h
    exact hv ((sub_eq_zero.mp h) ▸ w.property.1)
  obtain ⟨l₀, hl⟩ := Module.exists_dual_forall_apply_ne_zero (K := ℂ)
    (fun w : K => v - w.val) hn
  let l : V →L[ℂ] ℂ := l₀.toContinuousLinearMap
  have hsep : ∀ w ∈ S, L w = L v → l w ≠ l v := by
    intro w hw hLw heq
    have h := hl ⟨w, hw, hLw⟩
    change l (v - w) ≠ 0 at h
    apply h
    rw [map_sub, heq, sub_self]
  obtain ⟨w, hw⟩ := hsurj (L v)
  change L w.val = L v at hw
  have hL : Function.Surjective L := fun y => by
    obtain ⟨u, hu⟩ := hsurj y
    exact ⟨u, hu⟩
  refine ⟨l, surjective_prod L hL l (v := v - w.val) ?_ (hl ⟨w, w.property, hw⟩), hsep⟩
  rw [map_sub, hw, sub_self]

end Geometry.ComplexTorus.RiemannProjectivity.SeparatingLinearCoordinates.Constructions.LinearSeparation

namespace Geometry.ComplexTorus.RiemannProjectivity.SeparatingLinearCoordinates.Constructions.SeparatingCoordinates

/-! # RiemannProjectivity: linear coordinates nonzero on every vector in a finite list -/

open Set _root_.Module

section Algebraic

variable {V ι : Type*} [AddCommGroup V] [Module ℂ V] [Finite ι]

theorem span_good_duals (v : ι → V) (hv : ∀ i, v i ≠ 0) :
    Submodule.span ℂ {l : Module.Dual ℂ V | ∀ i, l (v i) ≠ 0} = ⊤ := by
  classical
  let G := {l : Module.Dual ℂ V | ∀ i, l (v i) ≠ 0}
  by_contra hG
  let P : Option ι → Submodule ℂ (Module.Dual ℂ V)
    | none => Submodule.span ℂ G
    | some i => LinearMap.ker (Module.Dual.eval ℂ V (v i))
  have hP : ∀ i, P i ≠ ⊤ := by
    rintro (_ | i)
    · exact hG
    · obtain ⟨l, hl⟩ := Module.Projective.exists_dual_ne_zero ℂ (hv i)
      intro htop
      have hmem : l ∈ P (some i) := htop ▸ Submodule.mem_top
      exact hl hmem
  obtain ⟨l, hl⟩ := Submodule.exists_forall_notMem_of_forall_ne_top P hP
  have hlG : l ∈ G := fun i => hl (some i)
  exact hl none (Submodule.subset_span hlG)

end Algebraic

variable {V ι : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V] [Finite ι]

theorem exists_coordinates (v : ι → V) (hv : ∀ i, v i ≠ 0) :
    ∃ (m : ℕ) (e : V ≃L[ℂ] (Fin m → ℂ)), ∀ i j, e (v i) j ≠ 0 := by
  classical
  let G := {l : Module.Dual ℂ V | ∀ i, l (v i) ≠ 0}
  have hspan : ⊤ ≤ Submodule.span ℂ G := (span_good_duals v hv).ge
  let b₀ := Module.Basis.ofSpan hspan
  let m := finrank ℂ (Module.Dual ℂ V)
  let b : Module.Basis (Fin m) ℂ (Module.Dual ℂ V) :=
    b₀.reindex (b₀.indexEquiv (Module.finBasis ℂ (Module.Dual ℂ V)))
  have hb (j : Fin m) : b j ∈ G := by
    apply Module.Basis.ofSpan_subset hspan
    exact ⟨(b₀.indexEquiv (Module.finBasis ℂ (Module.Dual ℂ V))).symm j, by simp [b, b₀]⟩
  let M : V →ₗ[ℂ] (Fin m → ℂ) := LinearMap.pi (fun j => b j)
  have hMi : Function.Injective M := by
    apply (injective_iff_map_eq_zero M).mpr
    intro w hw
    apply (Module.forall_dual_apply_eq_zero_iff ℂ w).mp
    have he : Module.Dual.eval ℂ V w = 0 := b.ext (fun j => congrFun hw j)
    intro l
    exact DFunLike.congr_fun he l
  have hdim : finrank ℂ V = finrank ℂ (Fin m → ℂ) := by simp [m]
  have hMs : Function.Surjective M :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hMi
  let e : V ≃L[ℂ] (Fin m → ℂ) := ContinuousLinearEquiv.ofBijective M.toContinuousLinearMap
    (LinearMap.ker_eq_bot.mpr hMi) (LinearMap.range_eq_top.mpr hMs)
  exact ⟨m, e, fun i j => hb j i⟩

end Geometry.ComplexTorus.RiemannProjectivity.SeparatingLinearCoordinates.Constructions.SeparatingCoordinates

namespace Geometry.ComplexTorus.RiemannProjectivity.SeparatingLinearCoordinates.Constructions.SeparatingFiberCoordinates

/-! # RiemannProjectivity: complementary projection coordinates separating every other fiber point -/

open Set

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
  [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℂ W]

def coordinate {m : ℕ} (e : V ≃L[ℂ] (W × (Fin m → ℂ))) (j : Fin m) : V →L[ℂ] ℂ :=
  (ContinuousLinearMap.proj j).comp ((ContinuousLinearMap.snd ℂ W (Fin m → ℂ)).comp e.toContinuousLinearMap)

omit [FiniteDimensional ℂ V] [FiniteDimensional ℂ W] in
theorem coordinate_apply {m : ℕ} (e : V ≃L[ℂ] (W × (Fin m → ℂ))) (j : Fin m) (v : V) :
    coordinate e j v = (e v).2 j := rfl

omit [FiniteDimensional ℂ V] [FiniteDimensional ℂ W] in
theorem coordinate_pair_surjective (L : V →L[ℂ] W) {m : ℕ}
    (e : V ≃L[ℂ] (W × (Fin m → ℂ))) (he : ∀ v, (e v).1 = L v) (j : Fin m) :
    Function.Surjective (L.prod (coordinate e j)) := by
  rintro ⟨y, z⟩
  refine ⟨e.symm (y, Pi.single j z), Prod.ext ?_ ?_⟩
  · change L (e.symm (y, Pi.single j z)) = y
    rw [← he, e.apply_symm_apply]
  · change (e (e.symm (y, Pi.single j z))).2 j = z
    rw [e.apply_symm_apply]
    simp

theorem exists_split (L : V →L[ℂ] W) (hL : Function.Surjective L) {S : Set V} (v : V)
    (hfinite : {w : V | w ∈ S ∧ L w = L v}.Finite) :
    ∃ (m : ℕ) (e : V ≃L[ℂ] (W × (Fin m → ℂ))),
      (∀ w, (e w).1 = L w) ∧
      ∀ w ∈ S, L w = L v → w ≠ v → ∀ j : Fin m, coordinate e j w ≠ coordinate e j v := by
  classical
  obtain ⟨r, b, hb⟩ := AnalyticCone.Constructions.AnalyticConeImage.projection_coordinates L hL
  let K := {w : V | w ∈ S ∧ L w = L v ∧ w ≠ v}
  let : Fintype K := (hfinite.subset (fun _ hw => ⟨hw.1, hw.2.1⟩)).fintype
  have hnonzero (w : K) : (b (w.val - v)).2 ≠ 0 := by
    intro hwzero
    have hbzero : b (w.val - v) = 0 := by
      apply Prod.ext
      · change (b (w.val - v)).1 = 0
        rw [hb, map_sub, w.property.2.1, sub_self]
      · exact hwzero
    have hwv : w.val - v = 0 := b.injective (hbzero.trans b.map_zero.symm)
    exact w.property.2.2 (sub_eq_zero.mp hwv)
  obtain ⟨m, a, ha⟩ := SeparatingCoordinates.exists_coordinates (fun w : K => (b (w.val - v)).2) hnonzero
  let e := b.trans ((ContinuousLinearEquiv.refl ℂ W).prodCongr a)
  refine ⟨m, e, hb, ?_⟩
  intro w hw hLw hwv j heq
  have h := ha (⟨w, hw, hLw, hwv⟩ : K) j
  change (e (w - v)).2 j ≠ 0 at h
  apply h
  rw [map_sub]
  change coordinate e j w - coordinate e j v = 0
  rw [heq, sub_self]

end Geometry.ComplexTorus.RiemannProjectivity.SeparatingLinearCoordinates.Constructions.SeparatingFiberCoordinates

end

end OAI
