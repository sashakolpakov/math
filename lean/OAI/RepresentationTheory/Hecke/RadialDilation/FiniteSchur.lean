import OAI.RepresentationTheory.Hecke.RadialDilation.FiniteHeisenberg
import Mathlib.NumberTheory.Padics.HeightOneSpectrum

/-! # Finite Schur -/

namespace OAI.RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization

noncomputable section

section

/-! Scalar uniqueness on the actual finite-adelic Schwartz space. -/

open scoped Classical _root_.Matrix
open _root_.Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {MpR MpF MpA : Type*} [Group MpR] [Group MpF] [Group MpA]

theorem commuting_operator_coset_eigenvector (D : Theta.PoissonAutomorphyNormalizationData.WeilData ι MpR MpF MpA)
    (T : Theta.PoissonAutomorphyNormalizationData.finiteSchwartz ι →ₗ[ℂ] Theta.PoissonAutomorphyNormalizationData.finiteSchwartz ι) (hT : FiniteHeisenberg.Realization.CommutesFiniteHeisenberg D T)
    (q : ℚ) (hq : q ≠ 0) (a : ι → Theta.PoissonAutomorphyNormalizationData.AQf) :
    T (Theta.CosetTests.PoissonAutomorphyConstruction.latticeCosetTest q hq a) =
      (T (Theta.CosetTests.PoissonAutomorphyConstruction.latticeTestFunction q hq)).val 0 • Theta.CosetTests.PoissonAutomorphyConstruction.latticeCosetTest q hq a := by
  have hfix (x : ι → Theta.PoissonAutomorphyNormalizationData.AQf) : (Theta.CosetTests.PoissonAutomorphyConstruction.latticeCosetTest q hq a).val x =
      Theta.PoissonAutomorphyNormalizationData.heisenberg D.finiteCharacter 0 a (Theta.CosetTests.PoissonAutomorphyConstruction.latticeTestFunction q hq).val x := by
    rw [FiniteHeisenberg.Realization.finite_heisenberg_translation]
    rfl
  apply Subtype.ext
  funext x
  have h := hT 0 a (Theta.CosetTests.PoissonAutomorphyConstruction.latticeTestFunction q hq) (Theta.CosetTests.PoissonAutomorphyConstruction.latticeCosetTest q hq a) hfix x
  rw [FiniteHeisenberg.Realization.finite_heisenberg_translation, FiniteHeisenberg.Realization.commuting_operator_lattice_eigenvector D T hT] at h
  exact h

theorem commuting_operator_periodic_eigenvector (D : Theta.PoissonAutomorphyNormalizationData.WeilData ι MpR MpF MpA)
    (T : Theta.PoissonAutomorphyNormalizationData.finiteSchwartz ι →ₗ[ℂ] Theta.PoissonAutomorphyNormalizationData.finiteSchwartz ι) (hT : FiniteHeisenberg.Realization.CommutesFiniteHeisenberg D T)
    (q : ℚ) (hq : q ≠ 0) (φ : Theta.PoissonAutomorphyNormalizationData.finiteSchwartz ι)
    (hp : ∀ u ∈ Theta.PoissonAutomorphyFiniteFourier.Construction.finiteLattice q hq, ∀ x, φ.val (u + x) = φ.val x) :
    T φ = (T (Theta.CosetTests.PoissonAutomorphyConstruction.latticeTestFunction q hq)).val 0 • φ := by
  obtain ⟨s, hs⟩ := Theta.PoissonAutomorphyFiniteFourier.Construction.finiteSchwartz_coset_expansion φ q hq hp
  let a : Theta.PoissonAutomorphyFiniteFourier.Construction.FiniteQuotient (ι := ι) q hq → (ι → Theta.PoissonAutomorphyNormalizationData.AQf) :=
    fun c => Theta.PoissonAutomorphyNormalizationData.finiteDiagonal (Theta.PoissonAutomorphyFiniteFourier.Construction.finiteQuotientRep q hq c)
  have hφ : φ = ∑ c ∈ s, φ.val (a c) • Theta.CosetTests.PoissonAutomorphyConstruction.latticeCosetTest q hq (a c) := by
    apply Subtype.ext
    funext x
    simpa only [Submodule.coe_sum, Finset.sum_apply, Submodule.coe_smul,
      Pi.smul_apply, smul_eq_mul, Theta.CosetTests.PoissonAutomorphyConstruction.latticeCosetTest_apply] using hs x
  rw [hφ, map_sum, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro c _
  rw [map_smul, commuting_operator_coset_eigenvector D T hT, smul_smul, smul_smul, mul_comm]

/-- A linear operator commuting with finite-adelic translations and
modulations is one scalar on the full, concrete test space. -/
theorem finite_heisenberg_commutant_scalar (D : Theta.PoissonAutomorphyNormalizationData.WeilData ι MpR MpF MpA)
    (T : Theta.PoissonAutomorphyNormalizationData.finiteSchwartz ι →ₗ[ℂ] Theta.PoissonAutomorphyNormalizationData.finiteSchwartz ι) (hT : FiniteHeisenberg.Realization.CommutesFiniteHeisenberg D T) :
    ∀ φ : Theta.PoissonAutomorphyNormalizationData.finiteSchwartz ι, T φ = (T Theta.PoissonAutomorphyFiniteFourier.Construction.integralTestFunction).val 0 • φ := by
  intro φ
  obtain ⟨n, hn, hp⟩ := Theta.PoissonAutomorphyFiniteFourier.Construction.finiteSchwartz_lattice_period φ
  let hq : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
  have href : ∀ u ∈ Theta.PoissonAutomorphyFiniteFourier.Construction.finiteLattice (n : ℚ) hq, ∀ x,
      (Theta.PoissonAutomorphyFiniteFourier.Construction.integralTestFunction (ι := ι)).val (u + x) = Theta.PoissonAutomorphyFiniteFourier.Construction.integralTestFunction.val x := by
    intro u hu x
    exact Theta.PoissonAutomorphyFiniteFourier.Construction.integralIndicator_add (Theta.PoissonAutomorphyFiniteFourier.Construction.finiteLattice_nat_subset_integral n hn hu) x
  have h := commuting_operator_periodic_eigenvector D T hT (n : ℚ) hq Theta.PoissonAutomorphyFiniteFourier.Construction.integralTestFunction href
  have he := congrArg (fun f : Theta.PoissonAutomorphyNormalizationData.finiteSchwartz ι => f.val 0) h
  change (T Theta.PoissonAutomorphyFiniteFourier.Construction.integralTestFunction).val 0 =
    (T (Theta.CosetTests.PoissonAutomorphyConstruction.latticeTestFunction (n : ℚ) hq)).val 0 * Theta.PoissonAutomorphyFiniteFourier.Construction.integralIndicator 0 at he
  rw [Theta.PoissonAutomorphyFiniteFourier.Construction.integralIndicator_of_mem Theta.PoissonAutomorphyFiniteFourier.Construction.integralVectors.zero_mem, mul_one] at he
  rw [he]
  exact commuting_operator_periodic_eigenvector D T hT (n : ℚ) hq φ hp

end

section

/-! Actual Heisenberg operators preserve the finite-adelic test space. -/

open scoped Classical _root_.Topology _root_.Matrix
open _root_.Matrix Filter

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {MpR MpF MpA : Type*} [Group MpR] [Group MpF] [Group MpA]

theorem finiteCharacter_locallyConstant (D : Theta.PoissonAutomorphyNormalizationData.WeilData ι MpR MpF MpA) :
    IsLocallyConstant (D.finiteCharacter : Theta.PoissonAutomorphyNormalizationData.AQf → ℂ) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  have hnear : ∀ᶠ y : Theta.PoissonAutomorphyNormalizationData.AQf in 𝓝 x, y - x ∈ Theta.AdelicSupport.PoissonAutomorphyConstruction.integralAdele :=
    (Theta.AdelicSupport.PoissonAutomorphyConstruction.isOpen_integralAdele.preimage (continuous_id.sub continuous_const)).mem_nhds (by simp)
  filter_upwards [hnear] with y hy
  have h := D.finiteCharacter.map_add_eq_mul (y - x) x
  rw [sub_add_cancel, Theta.PoissonAutomorphyFiniteFourier.Construction.finiteCharacter_integral D _ hy, one_mul] at h
  exact h

theorem finiteHeisenberg_mem (D : Theta.PoissonAutomorphyNormalizationData.WeilData ι MpR MpF MpA)
    (p q : ι → Theta.PoissonAutomorphyNormalizationData.AQf) (f : Theta.PoissonAutomorphyNormalizationData.finiteSchwartz ι) :
    Theta.PoissonAutomorphyNormalizationData.heisenberg D.finiteCharacter p q f.val ∈ Theta.PoissonAutomorphyNormalizationData.finiteSchwartz ι := by
  obtain ⟨hf, hc⟩ := (Theta.PoissonAutomorphyNormalizationData.Construction.finiteSchwartz_mem_iff f.val).mp f.property
  apply (Theta.PoissonAutomorphyNormalizationData.Construction.finiteSchwartz_mem_iff _).mpr
  constructor
  · exact ((finiteCharacter_locallyConstant D).comp_continuous (by fun_prop)).mul
      (hf.comp_continuous (by fun_prop))
  · have hs : HasCompactSupport (fun x : ι → Theta.PoissonAutomorphyNormalizationData.AQf => f.val (fun i => x i - q i)) := by
      have he : (fun x : ι → Theta.PoissonAutomorphyNormalizationData.AQf => f.val (fun i => x i - q i)) =
          f.val ∘ Homeomorph.addRight (-q) := by
        funext x
        apply congrArg f.val
        funext i
        exact sub_eq_add_neg _ _
      rw [he]
      exact hc.comp_homeomorph (Homeomorph.addRight (-q))
    exact hs.mul_left

def finiteHeisenbergOperator (D : Theta.PoissonAutomorphyNormalizationData.WeilData ι MpR MpF MpA) (p q : ι → Theta.PoissonAutomorphyNormalizationData.AQf) :
    Theta.PoissonAutomorphyNormalizationData.finiteSchwartz ι →ₗ[ℂ] Theta.PoissonAutomorphyNormalizationData.finiteSchwartz ι where
  toFun f := ⟨Theta.PoissonAutomorphyNormalizationData.heisenberg D.finiteCharacter p q f.val, finiteHeisenberg_mem D p q f⟩
  map_add' f h := by
    apply Subtype.ext
    funext x
    exact mul_add _ _ _
  map_smul' c f := by
    apply Subtype.ext
    funext x
    exact mul_left_comm _ _ _

end

section

/-! Uniqueness of actual finite-adelic Heisenberg intertwiners. -/

open scoped Classical _root_.Matrix
open _root_.Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {MpR MpF MpA : Type*} [Group MpR] [Group MpF] [Group MpA]

theorem finite_intertwiners_scalar (D : Theta.PoissonAutomorphyNormalizationData.WeilData ι MpR MpF MpA)
    (g : Theta.PoissonAutomorphyNormalizationData.Sp ι Theta.PoissonAutomorphyNormalizationData.AQf) (U V : Theta.PoissonAutomorphyNormalizationData.finiteSchwartz ι ≃ₗ[ℂ] Theta.PoissonAutomorphyNormalizationData.finiteSchwartz ι)
    (hU : Theta.PoissonAutomorphyNormalizationData.IntertwinesHeisenberg D.finiteCharacter (Theta.PoissonAutomorphyNormalizationData.finiteSchwartz ι) g U)
    (hV : Theta.PoissonAutomorphyNormalizationData.IntertwinesHeisenberg D.finiteCharacter (Theta.PoissonAutomorphyNormalizationData.finiteSchwartz ι) g V) :
    ∃ c : ℂ, c ≠ 0 ∧ ∀ f : Theta.PoissonAutomorphyNormalizationData.finiteSchwartz ι, U f = c • V f := by
  let T : Theta.PoissonAutomorphyNormalizationData.finiteSchwartz ι →ₗ[ℂ] Theta.PoissonAutomorphyNormalizationData.finiteSchwartz ι := V.symm.toLinearMap.comp U.toLinearMap
  have hVT (f : Theta.PoissonAutomorphyNormalizationData.finiteSchwartz ι) : V (T f) = U f := by simp [T]
  have hT : FiniteHeisenberg.Realization.CommutesFiniteHeisenberg D T := by
    intro p q f h hh x
    let k := finiteHeisenbergOperator D p q (T f)
    have hvk : V k = U h := by
      apply Subtype.ext
      funext y
      have hv := hV p q (T f) k (fun _ => rfl) y
      have hu := hU p q f h hh y
      rw [hVT] at hv
      exact hv.trans hu.symm
    have hk : T h = k := V.injective (by rw [hVT]; exact hvk.symm)
    exact congrArg (fun f : Theta.PoissonAutomorphyNormalizationData.finiteSchwartz ι => f.val x) hk
  let c := (T Theta.PoissonAutomorphyFiniteFourier.Construction.integralTestFunction).val 0
  have hs (f : Theta.PoissonAutomorphyNormalizationData.finiteSchwartz ι) : T f = c • f := finite_heisenberg_commutant_scalar D T hT f
  have hc : c ≠ 0 := by
    intro hc
    have h := hs Theta.PoissonAutomorphyFiniteFourier.Construction.integralTestFunction
    rw [hc, zero_smul] at h
    have hf : (Theta.PoissonAutomorphyFiniteFourier.Construction.integralTestFunction : Theta.PoissonAutomorphyNormalizationData.finiteSchwartz ι) = 0 := by
      apply U.injective
      apply V.symm.injective
      change T Theta.PoissonAutomorphyFiniteFourier.Construction.integralTestFunction = T 0
      rw [map_zero]
      exact h
    have hh := congrArg (fun f : Theta.PoissonAutomorphyNormalizationData.finiteSchwartz ι => f.val 0) hf
    change Theta.PoissonAutomorphyFiniteFourier.Construction.integralIndicator (0 : ι → Theta.PoissonAutomorphyNormalizationData.AQf) = 0 at hh
    rw [Theta.PoissonAutomorphyFiniteFourier.Construction.integralIndicator_of_mem Theta.PoissonAutomorphyFiniteFourier.Construction.integralVectors.zero_mem] at hh
    exact one_ne_zero hh
  refine ⟨c, hc, ?_⟩
  intro f
  have h := congrArg V (hs f)
  rwa [hVT, map_smul] at h

end

section

/-! Scalar ambiguity disappears on the commutators defining the bare cover. -/

open scoped Classical _root_.Matrix commutatorElement
open _root_.Matrix

theorem scalar_equiv_inverse {S : Type*} [AddCommGroup S] [Module ℂ S]
    (U V : S ≃ₗ[ℂ] S) (c : ℂ) (hc : c ≠ 0) (hU : ∀ f, U f = c • V f) (f : S) :
    U.symm f = c⁻¹ • V.symm f := by
  apply U.injective
  rw [U.apply_symm_apply, hU, map_smul, V.apply_symm_apply, smul_smul,
    mul_inv_cancel₀ hc, one_smul]

theorem scalar_equiv_commutator {S : Type*} [AddCommGroup S] [Module ℂ S]
    (U V U₀ V₀ : S ≃ₗ[ℂ] S) (c d : ℂ) (hc : c ≠ 0) (hd : d ≠ 0)
    (hU : ∀ f, U f = c • U₀ f) (hV : ∀ f, V f = d • V₀ f) :
    ⁅U, V⁆ = ⁅U₀, V₀⁆ := by
  apply LinearEquiv.ext
  intro f
  change U (V (U.symm (V.symm f))) = U₀ (V₀ (U₀.symm (V₀.symm f)))
  rw [scalar_equiv_inverse V V₀ d hd hV, scalar_equiv_inverse U U₀ c hc hU]
  simp only [map_smul, hU, hV, smul_smul]
  have hcoef : c * (d * (c⁻¹ * d⁻¹)) = 1 := by
    field_simp
  simp only [hcoef, one_smul]

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {MpR MpF MpA : Type*} [Group MpR] [Group MpF] [Group MpA]

/-- Every commutator of finite-adelic intertwiners is an actual operator
in PoissonAutomorphy's two-fold cover. No chosen normalization of either input is needed. -/
theorem finite_commutator_lift (D : Theta.PoissonAutomorphyNormalizationData.WeilData ι MpR MpF MpA)
    (g h : Theta.PoissonAutomorphyNormalizationData.Sp ι Theta.PoissonAutomorphyNormalizationData.AQf) (U V : Theta.PoissonAutomorphyNormalizationData.finiteSchwartz ι ≃ₗ[ℂ] Theta.PoissonAutomorphyNormalizationData.finiteSchwartz ι)
    (hU : Theta.PoissonAutomorphyNormalizationData.IntertwinesHeisenberg D.finiteCharacter (Theta.PoissonAutomorphyNormalizationData.finiteSchwartz ι) g U)
    (hV : Theta.PoissonAutomorphyNormalizationData.IntertwinesHeisenberg D.finiteCharacter (Theta.PoissonAutomorphyNormalizationData.finiteSchwartz ι) h V) :
    ∃ m : MpF, D.finite.project m = ⁅g, h⁆ ∧ D.finite.action m = ⁅U, V⁆ := by
  obtain ⟨u, hu⟩ := D.finite.surjective g
  obtain ⟨v, hv⟩ := D.finite.surjective h
  have hDu := D.finite.intertwines u
  have hDv := D.finite.intertwines v
  rw [hu] at hDu
  rw [hv] at hDv
  obtain ⟨c, hc, hcu⟩ := finite_intertwiners_scalar D g U (D.finite.action u) hU hDu
  obtain ⟨d, hd, hdv⟩ := finite_intertwiners_scalar D h V (D.finite.action v) hV hDv
  refine ⟨⁅u, v⁆, ?_, ?_⟩
  · rw [map_commutatorElement, hu, hv]
  · rw [map_commutatorElement]
    exact (scalar_equiv_commutator U V (D.finite.action u) (D.finite.action v)
      c d hc hd hcu hdv).symm

end

section

/-! Exact passage from a bare intertwiner subgroup into PoissonAutomorphy's finite cover. -/

open scoped Classical _root_.Matrix commutatorElement
open _root_.Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {MpR MpF MpA : Type*} [Group MpR] [Group MpF] [Group MpA]

def finiteCoverPair (D : Theta.PoissonAutomorphyNormalizationData.WeilData ι MpR MpF MpA) :
    MpF →* (Theta.PoissonAutomorphyNormalizationData.Sp ι Theta.PoissonAutomorphyNormalizationData.AQf × (Theta.PoissonAutomorphyNormalizationData.finiteSchwartz ι ≃ₗ[ℂ] Theta.PoissonAutomorphyNormalizationData.finiteSchwartz ι)) :=
  D.finite.project.prod D.finite.action

theorem finiteCoverPair_minus (D : Theta.PoissonAutomorphyNormalizationData.WeilData ι MpR MpF MpA) :
    finiteCoverPair D D.finite.negOne = (1, LinearEquiv.neg ℂ) := by
  apply Prod.ext
  · exact D.finite.project_negOne
  · apply LinearEquiv.ext
    exact D.finite.genuine

/-- A homomorphism of actual intertwiners restricts to PoissonAutomorphy's two-fold cover
on the subgroup generated by commutators and negative identity. -/
theorem finite_bare_element_lift
    (D : Theta.PoissonAutomorphyNormalizationData.WeilData ι MpR MpF MpA) {G : Type*} [Group G] (z : G)
    (F : G →* (Theta.PoissonAutomorphyNormalizationData.Sp ι Theta.PoissonAutomorphyNormalizationData.AQf × (Theta.PoissonAutomorphyNormalizationData.finiteSchwartz ι ≃ₗ[ℂ] Theta.PoissonAutomorphyNormalizationData.finiteSchwartz ι)))
    (hF : ∀ g, Theta.PoissonAutomorphyNormalizationData.IntertwinesHeisenberg D.finiteCharacter (Theta.PoissonAutomorphyNormalizationData.finiteSchwartz ι) (F g).1 (F g).2)
    (hz : F z = (1, LinearEquiv.neg ℂ))
    (g : Subgroup.closure (commutatorSet G ∪ {z})) :
    ∃ m : MpF, finiteCoverPair D m = F g.val := by
  change F g.val ∈ (finiteCoverPair D).range
  change g.val ∈ (finiteCoverPair D).range.comap F
  apply ((Subgroup.closure_le _).mpr ?_) g.property
  intro x hx
  rcases hx with hx | hx
  · obtain ⟨u, v, rfl⟩ := mem_commutatorSet_iff.mp hx
    obtain ⟨m, hm, hma⟩ := finite_commutator_lift D (F u).1 (F v).1 (F u).2 (F v).2 (hF u) (hF v)
    refine ⟨m, ?_⟩
    rw [map_commutatorElement]
    exact Prod.ext hm hma
  · have hxz : x = z := hx
    subst x
    exact ⟨D.finite.negOne, (finiteCoverPair_minus D).trans hz.symm⟩

def finiteBareLift
    (D : Theta.PoissonAutomorphyNormalizationData.WeilData ι MpR MpF MpA) {G : Type*} [Group G] (z : G)
    (F : G →* (Theta.PoissonAutomorphyNormalizationData.Sp ι Theta.PoissonAutomorphyNormalizationData.AQf × (Theta.PoissonAutomorphyNormalizationData.finiteSchwartz ι ≃ₗ[ℂ] Theta.PoissonAutomorphyNormalizationData.finiteSchwartz ι)))
    (hF : ∀ g, Theta.PoissonAutomorphyNormalizationData.IntertwinesHeisenberg D.finiteCharacter (Theta.PoissonAutomorphyNormalizationData.finiteSchwartz ι) (F g).1 (F g).2)
    (hz : F z = (1, LinearEquiv.neg ℂ)) :
    Subgroup.closure (commutatorSet G ∪ {z}) →* MpF where
  toFun g := (finite_bare_element_lift D z F hF hz g).choose
  map_one' := by
    apply D.finite.faithful
    change finiteCoverPair D _ = finiteCoverPair D 1
    rw [(finite_bare_element_lift D z F hF hz 1).choose_spec, map_one]
    exact F.map_one
  map_mul' g h := by
    apply D.finite.faithful
    change finiteCoverPair D _ = finiteCoverPair D (_ * _)
    rw [(finite_bare_element_lift D z F hF hz (g * h)).choose_spec, map_mul,
      (finite_bare_element_lift D z F hF hz g).choose_spec,
      (finite_bare_element_lift D z F hF hz h).choose_spec]
    exact F.map_mul g.val h.val

theorem finiteBareLift_spec
    (D : Theta.PoissonAutomorphyNormalizationData.WeilData ι MpR MpF MpA) {G : Type*} [Group G] (z : G)
    (F : G →* (Theta.PoissonAutomorphyNormalizationData.Sp ι Theta.PoissonAutomorphyNormalizationData.AQf × (Theta.PoissonAutomorphyNormalizationData.finiteSchwartz ι ≃ₗ[ℂ] Theta.PoissonAutomorphyNormalizationData.finiteSchwartz ι)))
    (hF : ∀ g, Theta.PoissonAutomorphyNormalizationData.IntertwinesHeisenberg D.finiteCharacter (Theta.PoissonAutomorphyNormalizationData.finiteSchwartz ι) (F g).1 (F g).2)
    (hz : F z = (1, LinearEquiv.neg ℂ))
    (g : Subgroup.closure (commutatorSet G ∪ {z})) :
    finiteCoverPair D (finiteBareLift D z F hF hz g) = F g.val :=
  (finite_bare_element_lift D z F hF hz g).choose_spec

theorem finite_lifts_differ_by_sign (D : Theta.PoissonAutomorphyNormalizationData.WeilData ι MpR MpF MpA)
    (u v : MpF) (hp : D.finite.project u = D.finite.project v) :
    ∃ ε : ℂ, ε ^ 2 = 1 ∧ ∀ f : Theta.PoissonAutomorphyNormalizationData.finiteSchwartz ι,
      D.finite.action u f = ε • D.finite.action v f := by
  have hk : D.finite.project (u * v⁻¹) = 1 := by
    rw [map_mul, map_inv, hp, mul_inv_cancel]
  rcases (D.finite.kernel _).mp hk with h | h
  · have huv : u = v := mul_inv_eq_one.mp h
    refine ⟨1, by norm_num, ?_⟩
    intro f
    rw [huv, one_smul]
  · have huv : u = D.finite.negOne * v := mul_inv_eq_iff_eq_mul.mp h
    refine ⟨-1, by norm_num, ?_⟩
    intro f
    rw [huv, map_mul]
    change D.finite.action D.finite.negOne (D.finite.action v f) = (-1 : ℂ) • D.finite.action v f
    rw [D.finite.genuine]
    exact (neg_one_smul ℂ (D.finite.action v f)).symm

/-- Once the concrete tensor action covers the rational scalar, comparison
with PoissonAutomorphy's chosen finite lift introduces only a sign. -/
theorem finiteAction_bare_comparison
    (D : Theta.PoissonAutomorphyNormalizationData.WeilData ι MpR MpF MpA) {G : Type*} [Group G] (z : G)
    (F : G →* (Theta.PoissonAutomorphyNormalizationData.Sp ι Theta.PoissonAutomorphyNormalizationData.AQf × (Theta.PoissonAutomorphyNormalizationData.finiteSchwartz ι ≃ₗ[ℂ] Theta.PoissonAutomorphyNormalizationData.finiteSchwartz ι)))
    (hF : ∀ g, Theta.PoissonAutomorphyNormalizationData.IntertwinesHeisenberg D.finiteCharacter (Theta.PoissonAutomorphyNormalizationData.finiteSchwartz ι) (F g).1 (F g).2)
    (hz : F z = (1, LinearEquiv.neg ℂ))
    (g : Subgroup.closure (commutatorSet G ∪ {z}))
    (γ : Theta.PoissonAutomorphyNormalizationData.Sp ι ℚ) (hg : (F g.val).1 = Theta.PoissonAutomorphyNormalizationData.mapSp (algebraMap ℚ Theta.PoissonAutomorphyNormalizationData.AQf) γ) :
    ∃ ε : ℂ, ε ^ 2 = 1 ∧ ∀ f : Theta.PoissonAutomorphyNormalizationData.finiteSchwartz ι,
      D.finiteAction γ f = ε • (F g.val).2 f := by
  have hs := finiteBareLift_spec D z F hF hz g
  have hp := congrArg Prod.fst hs
  have ha := congrArg Prod.snd hs
  obtain ⟨ε, hε, haction⟩ := finite_lifts_differ_by_sign D
    (D.finiteLift γ) (finiteBareLift D z F hF hz g)
    ((D.finiteLift_covers γ).trans (hp.trans hg).symm)
  refine ⟨ε, hε, ?_⟩
  intro f
  have h := haction f
  change D.finiteAction γ f = ε • D.finite.action (finiteBareLift D z F hF hz g) f at h
  change D.finite.action (finiteBareLift D z F hF hz g) = (F g.val).2 at ha
  rwa [ha] at h

end

section

/-! Concrete continuous projection to, and inclusion of, a p-adic coordinate. -/

open scoped Classical RestrictedProduct _root_.Topology
open Filter IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

def finitePrimeEval (v : HeightOneSpectrum ℤ) : Theta.PoissonAutomorphyNormalizationData.AQf →+* v.adicCompletion ℚ :=
  RestrictedProduct.evalRingHom (fun w : HeightOneSpectrum ℤ => w.adicCompletion ℚ) v

def finitePrimeIncludeValue (v : HeightOneSpectrum ℤ) (x : v.adicCompletion ℚ) : Theta.PoissonAutomorphyNormalizationData.AQf :=
  RestrictedProduct.single (fun w : HeightOneSpectrum ℤ => w.adicCompletionIntegers ℚ) v x

def finitePrimeInclude (v : HeightOneSpectrum ℤ) : v.adicCompletion ℚ →ₗ[ℚ] Theta.PoissonAutomorphyNormalizationData.AQf where
  toFun := finitePrimeIncludeValue v
  map_add' x y := RestrictedProduct.single_add _ _ _ _
  map_smul' a x := by
    apply DFunLike.ext
    intro w
    have hsmul (b : Theta.PoissonAutomorphyNormalizationData.AQf) : finitePrimeEval w (a • b) = a • finitePrimeEval w b :=
      (finitePrimeEval w).toRatAlgHom.toLinearMap.map_smul a b
    change finitePrimeEval w (finitePrimeIncludeValue v (a • x)) =
      finitePrimeEval w (a • finitePrimeIncludeValue v x)
    rw [hsmul]
    change RestrictedProduct.single (fun z : HeightOneSpectrum ℤ => z.adicCompletionIntegers ℚ) v (a • x) w =
      a • RestrictedProduct.single (fun z : HeightOneSpectrum ℤ => z.adicCompletionIntegers ℚ) v x w
    by_cases hw : w = v
    · subst w
      rw [RestrictedProduct.single_eq_same, RestrictedProduct.single_eq_same]
    · rw [RestrictedProduct.single_eq_of_ne _ _ hw, RestrictedProduct.single_eq_of_ne _ _ hw]
      rw [Algebra.smul_def, mul_zero]

theorem finitePrimeEval_include (v : HeightOneSpectrum ℤ) (x : v.adicCompletion ℚ) :
    finitePrimeEval v (finitePrimeInclude v x) = x := by
  change RestrictedProduct.single (fun w : HeightOneSpectrum ℤ => w.adicCompletionIntegers ℚ) v x v = x
  exact RestrictedProduct.single_eq_same _ _ _

theorem finitePrimeEval_continuous (v : HeightOneSpectrum ℤ) : Continuous (finitePrimeEval v) :=
  RestrictedProduct.continuous_eval v

theorem finitePrimeInclude_continuous (v : HeightOneSpectrum ℤ) : Continuous (finitePrimeInclude v) := by
  let A := fun w : HeightOneSpectrum ℤ => (w.adicCompletionIntegers ℚ : Set (w.adicCompletion ℚ))
  let f : v.adicCompletion ℚ → RestrictedProduct (fun w : HeightOneSpectrum ℤ => w.adicCompletion ℚ)
      A (Filter.principal {w | w ≠ v}) := fun x =>
    ⟨Pi.single v x, by
      rw [Filter.eventually_principal]
      intro w hw
      simp [Pi.single_eq_of_ne hw, A]⟩
  have hf : Continuous f := by
    apply RestrictedProduct.continuous_rng_of_principal.mpr
    exact continuous_single v
  have hco : cofinite ≤ Filter.principal {w : HeightOneSpectrum ℤ | w ≠ v} := by
    rw [Filter.le_principal_iff, Filter.mem_cofinite]
    simp
  exact (RestrictedProduct.continuous_inclusion hco).comp hf

variable (q : ℕ) [Fact q.Prime]

def rationalPrime : HeightOneSpectrum ℤ :=
  (Rat.HeightOneSpectrum.primesEquiv (R := ℤ)).symm ⟨q, Fact.out⟩

def padicCoordinateEquiv : ℚ_[q] ≃A[ℚ] (rationalPrime q).adicCompletion ℚ :=
  Padic.adicCompletionEquiv ℤ ⟨q, Fact.out⟩

def finitePadicProjection : Theta.PoissonAutomorphyNormalizationData.AQf →ₐ[ℚ] ℚ_[q] :=
  ((padicCoordinateEquiv q).symm.toRingHom.comp (finitePrimeEval (rationalPrime q))).toRatAlgHom

def finitePadicInclusion : ℚ_[q] →ₗ[ℚ] Theta.PoissonAutomorphyNormalizationData.AQf :=
  (finitePrimeInclude (rationalPrime q)).comp (padicCoordinateEquiv q).toAlgEquiv.toLinearMap

theorem finitePadicProjection_inclusion (x : ℚ_[q]) :
    finitePadicProjection q (finitePadicInclusion q x) = x := by
  change (padicCoordinateEquiv q).symm
    (finitePrimeEval (rationalPrime q) (finitePrimeInclude (rationalPrime q) (padicCoordinateEquiv q x))) = x
  rw [finitePrimeEval_include, ContinuousAlgEquiv.symm_apply_apply]

theorem finitePadicProjection_continuous : Continuous (finitePadicProjection q) :=
  (padicCoordinateEquiv q).symm.continuous.comp (finitePrimeEval_continuous (rationalPrime q))

theorem finitePadicInclusion_continuous : Continuous (finitePadicInclusion q) :=
  (finitePrimeInclude_continuous (rationalPrime q)).comp (padicCoordinateEquiv q).continuous

end

/-! The local p-adic character is the restriction of the actual adelic character. -/

open scoped Classical

theorem compact_subring_norm_le_one {K : Type*} [NormedField K]
    (A : Subring K) (hA : IsCompact (A : Set K)) {x : K} (hx : x ∈ A) : ‖x‖ ≤ 1 := by
  obtain ⟨C, hC⟩ := (hA.image continuous_norm).bddAbove
  by_contra h
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt C (lt_of_not_ge h)
  have hp := hC (Set.mem_image_of_mem (fun z : K => ‖z‖) (A.pow_mem hx n))
  rw [norm_pow] at hp
  exact (not_lt_of_ge hp) hn

variable (q : ℕ) [Fact q.Prime]

theorem finitePadicProjection_integral_norm (a : Theta.PoissonAutomorphyNormalizationData.AQf) (ha : a ∈ Theta.AdelicSupport.PoissonAutomorphyConstruction.integralAdele) :
    ‖finitePadicProjection q a‖ ≤ 1 := by
  apply compact_subring_norm_le_one (Theta.AdelicSupport.PoissonAutomorphyConstruction.integralAdele.map (finitePadicProjection q).toRingHom)
  · exact Theta.IntegralAdeles.PoissonAutomorphyConstruction.isCompact_integralAdele.image (finitePadicProjection_continuous q)
  · exact ⟨a, ha, rfl⟩

theorem finitePadicInclusion_inverse_prime_not_integral :
    finitePadicInclusion q (q : ℚ_[q])⁻¹ ∉ Theta.AdelicSupport.PoissonAutomorphyConstruction.integralAdele := by
  intro hi
  have hn := finitePadicProjection_integral_norm q _ hi
  rw [finitePadicProjection_inclusion, norm_inv, Padic.norm_p, inv_inv] at hn
  have hq : (1 : ℝ) < q := by exact_mod_cast (Fact.out : q.Prime).one_lt
  exact (not_lt_of_ge hn) hq

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {MpR MpF MpA : Type*} [Group MpR] [Group MpF] [Group MpA]
  (D : Theta.PoissonAutomorphyNormalizationData.WeilData ι MpR MpF MpA)

def finiteLocalCharacter : AddChar ℚ_[q] ℂ :=
  D.finiteCharacter.compAddMonoidHom (finitePadicInclusion q).toAddMonoidHom

theorem finiteLocalCharacter_apply (x : ℚ_[q]) :
    finiteLocalCharacter q D x = D.finiteCharacter (finitePadicInclusion q x) := rfl

theorem finiteLocalCharacter_continuous : Continuous (finiteLocalCharacter q D) :=
  (Theta.PoissonAutomorphyFiniteFourier.Construction.finiteCharacter_continuous D).comp (finitePadicInclusion_continuous q)

theorem finiteLocalCharacter_unitary (x : ℚ_[q]) : ‖finiteLocalCharacter q D x‖ = 1 := by
  change ‖D.finiteCharacter (finitePadicInclusion q x)‖ = 1
  rw [D.finiteCharacter_eq]
  exact D.character_unitary _

theorem finiteLocalCharacter_nontrivial : ∃ x, finiteLocalCharacter q D x ≠ 1 := by
  refine ⟨(q : ℚ_[q])⁻¹, ?_⟩
  intro h
  rw [finiteLocalCharacter_apply] at h
  exact finitePadicInclusion_inverse_prime_not_integral q ((Theta.PoissonAutomorphyFiniteFourier.Construction.finiteCharacter_eq_one_iff D _).mp h)

end

end OAI.RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization
