import OAI.AlgebraicGeometry.ComplexPoints.IntegralCharacters
import Mathlib.Analysis.Normed.Field.Approximation

/-! # Open Integral Map -/

namespace OAI.AlgebraicGeometry.ComplexPoints.OpenIntegralMap.ClosednessConstruction

/-! Closedness: openness on complex points of integral maps to a normal affine base.
The elementary root-persistence argument also appears in
`Proofs/RootContinuity.lean`; it is included here with independent imports. -/

open Set _root_.Polynomial _root_.Metric
open scoped _root_.Topology BigOperators

theorem root_near_of_small_eval {p : ℂ[X]} (hp : p.Monic) {z : ℂ} {ε : ℝ}
    (hε : 0 < ε) (heval : ‖p.eval z‖ < ε ^ p.natDegree) :
    ∃ w, p.eval w = 0 ∧ dist z w < ε := by
  by_contra! hn
  have hle := Multiset.prod_map_le_prod_map₀ (s := p.roots)
    (fun _ : ℂ => ε) (fun w => ‖z - w‖) (fun _ _ => hε.le)
    (fun w hw => by simpa only [dist_eq_norm] using hn w ((mem_roots hp.ne_zero).mp hw))
  have hprod : (p.roots.map (fun w => ‖z - w‖)).prod = ‖p.eval z‖ := by
    rw [(IsAlgClosed.splits p).eval_eq_prod_roots_of_monic hp]
    exact p.roots.prod_hom' (NormedField.toMulRingNorm ℂ) (fun w => z - w)
  rw [hprod, Multiset.map_const', Multiset.prod_replicate,
    ← (IsAlgClosed.splits p).natDegree_eq_card_roots] at hle
  exact heval.not_ge hle

theorem continuousAt_monic_family_eval {V : Type*} [TopologicalSpace V]
    {P : V → ℂ[X]} {x : V} (d : ℕ) (hd : ∀ y, (P y).natDegree ≤ d)
    (hcoeff : ∀ j, ContinuousAt (fun y => (P y).coeff j) x) (z : ℂ) :
    ContinuousAt (fun y => (P y).eval z) x := by
  have heq : (fun y => (P y).eval z) =
      fun y => ∑ j ∈ Finset.range (d + 1), (P y).coeff j * z ^ j := by
    funext y
    exact eval_eq_sum_range' (Nat.lt_succ_of_le (hd y)) z
  rw [heq]
  exact tendsto_finsetSum _ (fun j _ => (hcoeff j).mul continuousAt_const)

theorem eventually_monic_root_near {V : Type*} [TopologicalSpace V]
    {P : V → ℂ[X]} {x : V} (k : ℕ)
    (hp : ∀ y, (P y).Monic ∧ (P y).natDegree = k)
    (hcoeff : ∀ j, ContinuousAt (fun y => (P y).coeff j) x)
    {z : ℂ} (hz : (P x).eval z = 0) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ y in 𝓝 x, ∃ w, (P y).eval w = 0 ∧ dist z w < ε := by
  have hc := (continuousAt_monic_family_eval k (fun y => (hp y).2.le) hcoeff z).norm
  have hsmall : ∀ᶠ y in 𝓝 x, ‖(P y).eval z‖ < ε ^ k :=
    hc.eventually_lt_const (by
      change ‖(P x).eval z‖ < ε ^ k
      rw [hz, norm_zero]
      exact pow_pos hε _)
  filter_upwards [hsmall] with y hy
  apply root_near_of_small_eval (hp y).1 hε
  simpa only [(hp y).2] using hy

variable {R B : Type*} [CommRing R] [Algebra ℂ R]
    [CommRing B] [Algebra ℂ B] [Algebra R B] [IsScalarTower ℂ R B]
    [IsDomain R] [IsIntegrallyClosed R] [IsDomain B] [Module.IsTorsionFree R B]
    [Algebra.IsIntegral R B] [Algebra.FiniteType ℂ B] [Algebra.FiniteType ℂ R]

/-- An integral map of complex affine domains to a normal base is open on
complex points. The proof uses finite fibers and persistence of monic roots. -/
theorem normal_integral_comap_isOpenMap :
    IsOpenMap (Foundations.Scheme.AffineComplexPoints.affineComplexPoints.comap (IsScalarTower.toAlgHom ℂ R B)) := by
  let f := IsScalarTower.toAlgHom ℂ R B
  have hf : f.toRingHom.IsIntegral := Algebra.isIntegral_def.mp inferInstance
  have hproper := IntegralTopology.ClosednessConstruction.integral_comap_isProperMap f hf
  intro U hU
  rw [isOpen_iff_mem_nhds]
  rintro _ ⟨p, hp, rfl⟩
  obtain ⟨b, hb⟩ := IntegralCharacters.ClosednessConstruction.exists_separating_element
    (Foundations.Scheme.AffineComplexPoints.affineComplexPoints.comap f ⁻¹' {Foundations.Scheme.AffineComplexPoints.affineComplexPoints.comap f p}) (IntegralCharacters.ClosednessConstruction.integral_comap_finite_fiber f hf _) p
  let F : Foundations.Scheme.AffineComplexPoints.affineComplexPoints B → Foundations.Scheme.AffineComplexPoints.affineComplexPoints R × ℂ :=
    fun x => (Foundations.Scheme.AffineComplexPoints.affineComplexPoints.comap f x, x b)
  have hF : IsProperMap F := isProperMap_of_comp_of_t2
    ((Foundations.Scheme.AffineComplexPoints.affineComplexPoints.comap f).continuous.prodMk (Foundations.Scheme.AffineComplexPoints.affineComplexPoints.continuous_eval b)) continuous_fst hproper
  have hclosed : IsClosed (F '' Uᶜ) := hF.isClosedMap Uᶜ hU.isClosed_compl
  have hpF : F p ∈ (F '' Uᶜ)ᶜ := by
    rintro ⟨q, hq, he⟩
    have hbase : Foundations.Scheme.AffineComplexPoints.affineComplexPoints.comap f q = Foundations.Scheme.AffineComplexPoints.affineComplexPoints.comap f p := congrArg Prod.fst he
    have hval : p b = q b := (congrArg Prod.snd he).symm
    have hpq := hb q hbase hval
    exact hq (hpq ▸ hp)
  obtain ⟨W, hW, V, hV, hWV⟩ := mem_nhds_prod_iff.mp
    (hclosed.isOpen_compl.mem_nhds hpF)
  obtain ⟨ε, hε, hεV⟩ := Metric.mem_nhds_iff.mp hV
  let P : Foundations.Scheme.AffineComplexPoints.affineComplexPoints R → ℂ[X] := fun y => (minpoly R b).map y.toRingHom
  have hmon : (minpoly R b).Monic := minpoly.monic (Algebra.IsIntegral.isIntegral b)
  have hroot : (P (Foundations.Scheme.AffineComplexPoints.affineComplexPoints.comap f p)).eval (p b) = 0 := by
    dsimp only [P]
    rw [Polynomial.eval_map]
    exact (Polynomial.hom_eval₂ (minpoly R b) (algebraMap R B) p.toRingHom b).symm.trans
      ((congrArg p.toRingHom (minpoly.aeval R b)).trans (map_zero _))
  have hev := eventually_monic_root_near (minpoly R b).natDegree
    (fun y : Foundations.Scheme.AffineComplexPoints.affineComplexPoints R => ⟨hmon.map y.toRingHom, hmon.natDegree_map _⟩)
    (fun j => by
      simp only [Polynomial.coeff_map]
      exact (Foundations.Scheme.AffineComplexPoints.affineComplexPoints.continuous_eval ((minpoly R b).coeff j)).continuousAt)
    hroot hε
  filter_upwards [hW, hev] with y hyW hy
  obtain ⟨z, hz, hdist⟩ := hy
  obtain ⟨x, hx, hxb⟩ := IntegralCharacters.ClosednessConstruction.minpoly_specialization_root_lifts b y z hz
  refine ⟨x, ?_, hx⟩
  by_contra hxU
  have hxy : F x ∈ W ×ˢ V := by
    refine ⟨?_, ?_⟩
    · change Foundations.Scheme.AffineComplexPoints.affineComplexPoints.comap f x ∈ W
      rwa [hx]
    · change x b ∈ V
      rw [hxb]
      exact hεV (by simpa only [mem_ball, dist_comm] using hdist)
  exact hWV hxy ⟨x, hxU, rfl⟩

end OAI.AlgebraicGeometry.ComplexPoints.OpenIntegralMap.ClosednessConstruction
