import OAI.RepresentationTheory.Weil.UnitarySplitting.LocalTest
import OAI.RepresentationTheory.Weil.UnitarySplitting.Weak
import OAI.RepresentationTheory.Weil.AdelicSplitting.Oscillator
import OAI.RepresentationTheory.Weil.AdelicSplitting.RestrictedLimits

/-! # Tensor Projective -/

namespace OAI

noncomputable section

namespace RepresentationTheory.Theta.Adelic.TensorProjective.Smoothness

/-! Removing a continuous scalar ambiguity over an open nonarchimedean
subgroup. The projective neighborhood used here is later supplied by the
actual Schrödinger coordinate calculations. -/

open Filter _root_.MeasureTheory
open scoped _root_.Topology

def vectorStabilizer {G S : Type*} [Group G] [AddCommGroup S] [Module ℂ S]
    (ρ : G →* (S ≃ₗ[ℂ] S)) (f : S) : Subgroup G where
  carrier := {g | ρ g f = f}
  one_mem' := by simp
  mul_mem' := by
    intro g h hg hh
    change ρ g f = f at hg
    change ρ h f = f at hh
    change ρ (g * h) f = f
    simp only [map_mul, LinearEquiv.mul_apply, hh, hg]
  inv_mem' := by
    intro g hg
    change ρ g f = f at hg
    change ρ g⁻¹ f = f
    have h := congrArg (ρ g).symm hg
    simpa only [LinearEquiv.symm_apply_apply, map_inv, LinearEquiv.coe_inv] using h.symm

theorem power_on_eigenvector
    {G S : Type*} [Group G] [AddCommGroup S] [Module ℂ S]
    (ρ : G →* (S ≃ₗ[ℂ] S)) (g : G) (f : S) (z : ℂ)
    (hz : ρ g f = z • f) (n : ℕ) : ρ (g ^ n) f = z ^ n • f := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, map_mul, LinearEquiv.mul_apply, hz, map_smul, ih,
      smul_smul, pow_succ, mul_comm z]

/-- If a continuous linear action preserves a vector's line near the
identity, an open subgroup fixes the vector itself. No smoothness or
locally constant scalar character is assumed. -/
theorem open_stabilizer_of_projective_neighborhood
    {G S : Type*} [Group G] [TopologicalSpace G]
    [NonarchimedeanGroup G]
    [NormedAddCommGroup S] [NormedSpace ℂ S]
    (ρ : G →* (S ≃ₗ[ℂ] S)) (f : S)
    (hc : Continuous (fun g : G => ρ g f))
    (hline : ∀ᶠ g in 𝓝 (1 : G), ∃ z : ℂ, ρ g f = z • f) :
    IsOpen {g : G | ρ g f = f} := by
  by_cases hf : f = 0
  · simp [hf]
  have hnorm : 0 < ‖f‖ := norm_pos_iff.mpr hf
  have hsmall : ∀ᶠ g in 𝓝 (1 : G), ‖ρ g f - f‖ < ‖f‖ / 2 := by
    have h : Tendsto (fun g : G => ‖ρ g f - f‖) (𝓝 1) (𝓝 0) := by
      simpa using (hc.sub (continuous_const (y := f))).norm.tendsto (1 : G)
    exact h.eventually (gt_mem_nhds (half_pos hnorm))
  obtain ⟨U, hU⟩ := NonarchimedeanGroup.is_nonarchimedean
    {g : G | (∃ z : ℂ, ρ g f = z • f) ∧ ‖ρ g f - f‖ < ‖f‖ / 2}
    (hline.and hsmall)
  have hfix : ∀ g ∈ U, ρ g f = f := by
    intro g hg
    obtain ⟨z, hz⟩ := (hU hg).1
    have hz1 : z = 1 := by
      apply Weil.UnitarySplitting.LocalTest.Construction.complex_eq_one_of_powers_near_one
      intro n
      have h := (hU (U.pow_mem hg n)).2
      rw [power_on_eigenvector ρ g f z hz n] at h
      have heq : z ^ n • f - f = (z ^ n - 1) • f := by simp [sub_smul]
      rw [heq, norm_smul] at h
      nlinarith
    simpa only [hz1, one_smul] using hz
  exact (vectorStabilizer ρ f).isOpen_of_mem_nhds
    (Filter.mem_of_superset (U.isOpen.mem_nhds U.one_mem) hfix)

variable (k : Type) [NormedField k] [LocallyCompactSpace k]
    [MeasurableSpace k] [BorelSpace k] [SecondCountableTopology k]
    (N : ℕ) (ψ : AddChar k ℂ)

/-- Actual oscillator orbits are continuous in L² by the defining strong
observation topology. This does not assert open vector stabilizers. -/
theorem local_orbit_L2_continuous (f : Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat k N) :
    Continuous (fun g : Weil.AdelicSplitting.Oscillator.Construction.LocalCover k N ψ =>
      Weil.UnitarySplitting.Weak.Construction.testToL2 k N (Weil.AdelicSplitting.Oscillator.Construction.localOperator k N ψ g f)) := by
  apply continuous_iff_continuousAt.mpr
  intro g
  apply tendsto_iff_dist_tendsto_zero.mpr
  let h := Weil.AdelicSplitting.Oscillator.Construction.localOperator k N ψ g f
  have ho : Continuous (Weil.AdelicSplitting.Oscillator.Construction.localObservations k N ψ) := continuous_induced_dom
  have hc : Continuous (fun a : Weil.AdelicSplitting.Oscillator.Construction.LocalCover k N ψ =>
      Real.sqrt (Weil.Local.FunctionsMetaplectic.Construction.l2Energy k N (Weil.AdelicSplitting.Oscillator.Construction.localOperator k N ψ a f - h))) :=
    (continuous_apply (f, h)).comp (continuous_fst.comp (continuous_snd.comp ho))
  have ht := hc.tendsto g
  have heq (a : Weil.AdelicSplitting.Oscillator.Construction.LocalCover k N ψ) :
      dist (Weil.UnitarySplitting.Weak.Construction.testToL2 k N (Weil.AdelicSplitting.Oscillator.Construction.localOperator k N ψ a f))
        (Weil.UnitarySplitting.Weak.Construction.testToL2 k N (Weil.AdelicSplitting.Oscillator.Construction.localOperator k N ψ g f)) =
        Real.sqrt (Weil.Local.FunctionsMetaplectic.Construction.l2Energy k N (Weil.AdelicSplitting.Oscillator.Construction.localOperator k N ψ a f - h)) := by
    rw [dist_eq_norm, ← map_sub, Weil.UnitarySplitting.Weak.Construction.testToL2_norm]
  simp_rw [heq]
  simpa [h, Weil.Local.FunctionsMetaplectic.Construction.l2Energy] using ht

end RepresentationTheory.Theta.Adelic.TensorProjective.Smoothness

namespace RepresentationTheory.Theta.Adelic.TensorProjective.Restricted

/-! The algebraic restricted tensor product with a specified reference
vector. Its action is induced by the actual local linear operators. -/

open Filter
open scoped TensorProduct _root_.Topology

variable {I : Type*} {S : I → Type*}
    [∀ i, AddCommGroup (S i)] [∀ i, Module ℂ (S i)]
    (vac : ∀ i, S i)

def restrictedTensor : Submodule ℂ (⨂[ℂ] i, S i) :=
  Submodule.span ℂ {x | ∃ f : ∀ i, S i,
    (∀ᶠ i in cofinite, f i = vac i) ∧ PiTensorProduct.tprod ℂ f = x}

def pure (f : ∀ i, S i) (hf : ∀ᶠ i in cofinite, f i = vac i) : restrictedTensor vac :=
  ⟨PiTensorProduct.tprod ℂ f, Submodule.subset_span ⟨f, hf, rfl⟩⟩

variable {G : I → Type*} [∀ i, Group (G i)]
    (K : ∀ i, Subgroup (G i)) (ρ : ∀ i, G i →* (S i ≃ₗ[ℂ] S i))

def fullAction : Weil.AdelicSplitting.RestrictedLimits.Construction.RestrictedGroup K →*
    ((⨂[ℂ] i, S i) ≃ₗ[ℂ] (⨂[ℂ] i, S i)) where
  toFun g := PiTensorProduct.congr (fun i => ρ i (g i))
  map_one' := by
    apply LinearEquiv.toLinearMap_injective
    apply PiTensorProduct.ext
    ext f
    simp
  map_mul' g h := by
    apply LinearEquiv.toLinearMap_injective
    apply PiTensorProduct.ext
    ext f
    simp

@[simp] theorem fullAction_pure (g : Weil.AdelicSplitting.RestrictedLimits.Construction.RestrictedGroup K)
    (f : ∀ i, S i) :
    fullAction K ρ g (PiTensorProduct.tprod ℂ f) =
      PiTensorProduct.tprod ℂ (fun i => ρ i (g i) (f i)) :=
  PiTensorProduct.congr_tprod _ _

variable (hunramified : ∀ᶠ i in cofinite, ∀ g ∈ K i, ρ i g (vac i) = vac i)

include hunramified in
theorem fullAction_mem (g : Weil.AdelicSplitting.RestrictedLimits.Construction.RestrictedGroup K)
    (x : ⨂[ℂ] i, S i) (hx : x ∈ restrictedTensor vac) :
    fullAction K ρ g x ∈ restrictedTensor vac := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, hf, rfl⟩ := hx
    rw [fullAction_pure]
    apply Submodule.subset_span
    refine ⟨_, ?_, rfl⟩
    filter_upwards [hunramified, g.property, hf] with i hi hg hfi
    rw [hfi]
    exact hi (g i) hg
  | zero => simpa only [map_zero] using (restrictedTensor vac).zero_mem
  | add x y _ _ hx hy => simpa only [map_add] using (restrictedTensor vac).add_mem hx hy
  | smul c x _ hx => simpa only [map_smul] using (restrictedTensor vac).smul_mem c hx

def action : Weil.AdelicSplitting.RestrictedLimits.Construction.RestrictedGroup K →*
    (restrictedTensor vac ≃ₗ[ℂ] restrictedTensor vac) where
  toFun g :=
    { toFun := fun x => ⟨fullAction K ρ g x.val, fullAction_mem vac K ρ hunramified g x.val x.property⟩
      invFun := fun x => ⟨fullAction K ρ g⁻¹ x.val,
        fullAction_mem vac K ρ hunramified g⁻¹ x.val x.property⟩
      left_inv := by intro x; apply Subtype.ext; simp
      right_inv := by intro x; apply Subtype.ext; simp
      map_add' := by intros; apply Subtype.ext; exact map_add _ _ _
      map_smul' := by intros; apply Subtype.ext; exact map_smul _ _ _ }
  map_one' := by
    apply LinearEquiv.ext
    intro x
    apply Subtype.ext
    change fullAction K ρ 1 x.val = x.val
    rw [map_one]
    rfl
  map_mul' g h := by
    apply LinearEquiv.ext
    intro x
    apply Subtype.ext
    exact LinearEquiv.congr_fun (map_mul (fullAction K ρ) g h) x.val

@[simp] theorem action_val (g : Weil.AdelicSplitting.RestrictedLimits.Construction.RestrictedGroup K)
    (x : restrictedTensor vac) :
    (action vac K ρ hunramified g x).val = fullAction K ρ g x.val := rfl

variable [∀ i, TopologicalSpace (G i)] [∀ i, IsTopologicalGroup (G i)]
    (hK : ∀ i, IsOpen (K i : Set (G i)))
    (hsmooth : ∀ i (f : S i), IsOpen {g : G i | ρ i g f = f})

include hK hsmooth hunramified in
theorem pure_stabilizer_open (f : ∀ i, S i) (hf : ∀ᶠ i in cofinite, f i = vac i) :
    IsOpen {g : Weil.AdelicSplitting.RestrictedLimits.Construction.RestrictedGroup K |
      fullAction K ρ g (PiTensorProduct.tprod ℂ f) = PiTensorProduct.tprod ℂ f} := by
  let : Fact (∀ i, IsOpen (K i : Set (G i))) := ⟨hK⟩
  let good := {i | (∀ g ∈ K i, ρ i g (vac i) = vac i) ∧ f i = vac i}
  have hgood : good ∈ cofinite := hunramified.and hf
  have hbad : goodᶜ.Finite := hgood
  have hbopen : IsOpen {g : Weil.AdelicSplitting.RestrictedLimits.Construction.RestrictedGroup K |
      ∀ i ∈ goodᶜ, ρ i (g i) (f i) = f i} := by
    have hh := hbad.isOpen_biInter (fun i _ =>
      (hsmooth i (f i)).preimage (RestrictedProduct.continuous_eval
        (A := fun i => (K i : Set (G i))) (𝓕 := cofinite) i))
    convert hh using 1
    ext g
    simp
  have ho : IsOpen {g : Weil.AdelicSplitting.RestrictedLimits.Construction.RestrictedGroup K |
      (∀ i, i ∈ good → g i ∈ K i) ∧ ∀ i ∈ goodᶜ, ρ i (g i) (f i) = f i} :=
    (RestrictedProduct.isOpen_forall_imp_mem hK).inter hbopen
  have h1 : (1 : Weil.AdelicSplitting.RestrictedLimits.Construction.RestrictedGroup K) ∈
      {g | (∀ i, i ∈ good → g i ∈ K i) ∧ ∀ i ∈ goodᶜ, ρ i (g i) (f i) = f i} := by
    constructor
    · exact fun i _ => (K i).one_mem
    · intro i _; simp
  apply (Smoothness.vectorStabilizer (fullAction K ρ)
    (PiTensorProduct.tprod ℂ f)).isOpen_of_mem_nhds
  filter_upwards [ho.mem_nhds h1] with g hg
  change fullAction K ρ g (PiTensorProduct.tprod ℂ f) = _
  rw [fullAction_pure]
  congr 1
  funext i
  by_cases hi : i ∈ good
  · rw [hi.2]
    exact hi.1 (g i) (hg.1 i hi)
  · exact hg.2 i hi

include hK hsmooth hunramified in
theorem action_smooth (x : restrictedTensor vac) :
    IsOpen {g : Weil.AdelicSplitting.RestrictedLimits.Construction.RestrictedGroup K |
      action vac K ρ hunramified g x = x} := by
  let : Fact (∀ i, IsOpen (K i : Set (G i))) := ⟨hK⟩
  have hfull : ∀ y ∈ restrictedTensor vac,
      IsOpen {g : Weil.AdelicSplitting.RestrictedLimits.Construction.RestrictedGroup K | fullAction K ρ g y = y} := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨f, hf, rfl⟩ := hy
      exact pure_stabilizer_open vac K ρ hunramified hK hsmooth f hf
    | zero => simp
    | add y z _ _ hy hz =>
      apply (Smoothness.vectorStabilizer (fullAction K ρ) (y + z)).isOpen_of_mem_nhds
      filter_upwards [hy.mem_nhds (x := 1) (by simp), hz.mem_nhds (x := 1) (by simp)] with g hg hgz
      change fullAction K ρ g (y + z) = y + z
      rw [map_add, hg, hgz]
    | smul c y _ hy =>
      apply (Smoothness.vectorStabilizer (fullAction K ρ) (c • y)).isOpen_of_mem_nhds
      filter_upwards [hy.mem_nhds (x := 1) (by simp)] with g hg
      change fullAction K ρ g (c • y) = c • y
      rw [map_smul, hg]
  convert hfull x.val x.property using 1
  ext g
  exact Subtype.ext_iff

end RepresentationTheory.Theta.Adelic.TensorProjective.Restricted

namespace RepresentationTheory.Theta.Adelic.TensorProjective.Evaluation

/-! Evaluation of a restricted tensor by a family of local functionals.
This supplies actual adelic function values for finite Schwartz tensors. -/

open Filter Function
open scoped TensorProduct Classical

variable {I : Type*} {S : I → Type*}
    [∀ i, AddCommGroup (S i)] [∀ i, Module ℂ (S i)]
    (vac : ∀ i, S i) (ell : ∀ i, S i →ₗ[ℂ] ℂ)
    (hell : ∀ᶠ i in cofinite, ell i (vac i) = 1)

omit [∀ i, Module ℂ (S i)] [∀ i, AddCommGroup (S i)] in
theorem update_eventually_vac_iff [DecidableEq I] (f : ∀ i, S i) (i : I) (x : S i) :
    (∀ᶠ j in cofinite, update f i x j = vac j) ↔ ∀ᶠ j in cofinite, f j = vac j := by
  have he : ∀ᶠ j in cofinite, update f i x j = f j := by
    filter_upwards [show ∀ᶠ j : I in cofinite, j ≠ i from by simp] with j hj
    exact update_of_ne hj _ _
  constructor
  · intro h
    filter_upwards [he, h] with j hej hj
    rwa [← hej]
  · intro h
    filter_upwards [he, h] with j hej hj
    rwa [hej]

include hell in
theorem evaluation_finite_support (f : ∀ i, S i) (hf : ∀ᶠ i in cofinite, f i = vac i) :
    HasFiniteMulSupport (fun i => ell i (f i)) := by
  have he : ∀ᶠ i in cofinite, ell i (f i) = 1 := by
    filter_upwards [hf, hell] with i hi helli
    rw [hi, helli]
  exact he

def value (f : ∀ i, S i) : ℂ :=
  if ∀ᶠ i in cofinite, f i = vac i then ∏ᶠ i, ell i (f i) else 0

include hell in
theorem value_update [DecidableEq I] (f : ∀ i, S i) (i : I) (x : S i) :
    value vac ell (update f i x) = ell i x *
      (if ∀ᶠ j in cofinite, f j = vac j then ∏ᶠ (j) (_ : j ≠ i), ell j (f j) else 0) := by
  by_cases hf : ∀ᶠ j in cofinite, f j = vac j
  · have hu := (update_eventually_vac_iff vac f i x).mpr hf
    rw [value, ite_eq_left hu, ite_eq_left hf]
    rw [← mul_finprod_cond_ne i (evaluation_finite_support vac ell hell _ hu)]
    rw [update_self]
    congr 1
    apply finprod_congr
    intro j
    apply finprod_congr
    intro hj
    rw [update_of_ne hj]
  · have hu := (update_eventually_vac_iff vac f i x).not.mpr hf
    simp only [value, ite_eq_right hu, ite_eq_right hf, mul_zero]

def evaluationMultilinear : MultilinearMap ℂ S ℂ where
  toFun := value vac ell
  map_update_add' := by
    intro _ f i x y
    rw [value_update vac ell hell, value_update vac ell hell, value_update vac ell hell, map_add, add_mul]
  map_update_smul' := by
    intro _ f i c x
    rw [value_update vac ell hell, value_update vac ell hell, map_smul]
    simp only [smul_eq_mul, mul_assoc]

def evaluate : Restricted.restrictedTensor vac →ₗ[ℂ] ℂ :=
  (PiTensorProduct.lift (evaluationMultilinear vac ell hell)).comp
    (Restricted.restrictedTensor vac).subtype

theorem evaluate_pure (f : ∀ i, S i) (hf : ∀ᶠ i in cofinite, f i = vac i) :
    evaluate vac ell hell (Restricted.pure vac f hf) =
      ∏ᶠ i, ell i (f i) := by
  change PiTensorProduct.lift (evaluationMultilinear vac ell hell) (PiTensorProduct.tprod ℂ f) = _
  rw [PiTensorProduct.lift.tprod]
  exact ite_eq_left hf

end RepresentationTheory.Theta.Adelic.TensorProjective.Evaluation

end

end OAI
