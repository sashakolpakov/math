import OAI.RepresentationTheory.Weil.AdelicSplitting.ArchimedeanPositionChart
import OAI.RepresentationTheory.Weil.AdelicSplitting.FiniteTestSupport
import OAI.RepresentationTheory.Weil.AdelicSplitting.RapidFunctions

/-! # Theta Test -/

namespace OAI.RepresentationTheory.Weil.AdelicSplitting

noncomputable section

section

/-! Factorization of actual restricted test-family values, including at
rational points, into their archimedean and finite functions. -/

open scoped Classical _root_.NumberField
open _root_.NumberField Filter

open OAI.RepresentationTheory.Weil.AdelicSplitting.RapidFunctions.LocalAnalysis

variable (F : Type) [Field F] [NumberField F] (N : ℕ)

def ThetaTest.Construction.mixedRationalPosition (q : Fin N → F) : Fin N → mixedEmbedding.mixedSpace F :=
  fun i => mixedEmbedding F (q i)

theorem ThetaTest.Construction.mixedRationalPosition_injective : Function.Injective (ThetaTest.Construction.mixedRationalPosition F N) := by
  intro q r h
  funext i
  exact mixedEmbedding_injective F (congrFun h i)

theorem RestrictedTestFamilies.Construction.RestrictedTestFamily.value_factorization (f : RestrictedTestFamilies.Construction.RestrictedTestFamily F N) (a : Fin N → ArchimedeanAdeles.Construction.Adeles F) :
    f.value F N a =
      (∏ v : InfinitePlace F, (f (.inl v)).val (fun i => (a i).1 v)) *
        f.finiteValue F N (fun i => (a i).2) := by
  have harch : HasProd (fun v : InfinitePlace F => f.localValue F N a (.inl v))
      (∏ v : InfinitePlace F, (f (.inl v)).val (fun i => (a i).1 v)) := hasProd_fintype _
  have hfin : HasProd
      (fun v : IsDedekindDomain.HeightOneSpectrum (𝓞 F) => f.localValue F N a (.inr v))
      (f.finiteValue F N (fun i => (a i).2)) := by
    apply Multipliable.hasProd
    exact multipliable_of_hasFiniteMulSupport (eventually_cofinite.mp
      (f.finite_localValue_eventually_one F N (fun i => (a i).2)))
  exact (f.localValue_hasProd F N a).unique (HasProd.sum harch hfin)

theorem RestrictedTestFamilies.Construction.RestrictedTestFamily.mixedProductRapid_rational (f : RestrictedTestFamilies.Construction.RestrictedTestFamily F N) (q : Fin N → F) :
    f.mixedProductRapid F N (ThetaTest.Construction.mixedRationalPosition F N q) =
      ∏ v : InfinitePlace F, (f (.inl v)).val (fun i => ArchimedeanAdeles.Construction.rationalScalar F (.inl v) (q i)) := by
  let x : ∀ v : InfinitePlace F, Local.FunctionsMetaplectic.Construction.Position v.Completion N :=
    fun v i => ArchimedeanAdeles.Construction.rationalScalar F (.inl v) (q i)
  have he : ThetaTest.Construction.mixedRationalPosition F N q = ArchimedeanPositionChart.Construction.archimedeanPositionChart F N x := by
    funext i
    exact (ArchimedeanAdeles.Construction.infiniteAdeleMixedHomeomorph_rational F (q i)).symm
  rw [he]
  change f.archimedeanProductRapid F N
      ((ArchimedeanPositionChart.Construction.archimedeanPositionChart F N).symm (ArchimedeanPositionChart.Construction.archimedeanPositionChart F N x)) = _
  rw [(ArchimedeanPositionChart.Construction.archimedeanPositionChart F N).symm_apply_apply]
  rfl

theorem RestrictedTestFamilies.Construction.RestrictedTestFamily.value_rational_factorization (f : RestrictedTestFamilies.Construction.RestrictedTestFamily F N) (q : Fin N → F) :
    f.value F N (fun i => algebraMap F (ArchimedeanAdeles.Construction.Adeles F) (q i)) =
      f.mixedProductRapid F N (ThetaTest.Construction.mixedRationalPosition F N q) *
        f.finiteValue F N (FiniteCosets.Construction.finiteRationalPosition q) := by
  rw [f.value_factorization F N, f.mixedProductRapid_rational F N]
  rfl

def RestrictedTestFamilies.Construction.RestrictedTestFamily.theta (f : RestrictedTestFamilies.Construction.RestrictedTestFamily F N) : ℂ :=
  ∑' q : Fin N → F, f.value F N (fun i => algebraMap F (ArchimedeanAdeles.Construction.Adeles F) (q i))

end

section

/-! Discrete Minkowski position lattices obtained by clearing a rational
denominator. These contain the rational support of each finite test function. -/

open scoped Classical _root_.NumberField
open _root_.NumberField

open OAI.RepresentationTheory.Weil.AdelicSplitting.RapidFunctions.LocalAnalysis

variable (F : Type) [Field F] [NumberField F] (N : ℕ)

def ThetaTest.Construction.mixedPositionLattice (r : F) : Submodule ℤ (Fin N → mixedEmbedding.mixedSpace F) where
  carrier := {x | ∀ i, mixedEmbedding F r * x i ∈ mixedEmbedding.integerLattice F}
  zero_mem' := by simp
  add_mem' hx hy i := by
    simpa only [Pi.add_apply, mul_add] using (mixedEmbedding.integerLattice F).add_mem (hx i) (hy i)
  smul_mem' z x hx i := by
    simpa only [Pi.smul_apply, mul_smul_comm] using (mixedEmbedding.integerLattice F).smul_mem z (hx i)

theorem ThetaTest.Construction.mixedPositionLattice_discrete (r : F) (hr : r ≠ 0) :
    DiscreteTopology (ThetaTest.Construction.mixedPositionLattice F N r) := by
  let e : ThetaTest.Construction.mixedPositionLattice F N r → (Fin N → mixedEmbedding.integerLattice F) :=
    fun x i => ⟨mixedEmbedding F r * x.val i, x.property i⟩
  have he : Continuous e := continuous_pi (fun i =>
    (continuous_const.mul ((continuous_apply i).comp continuous_subtype_val)).subtype_mk _)
  apply DiscreteTopology.of_continuous_injective he
  intro x y h
  apply Subtype.ext
  funext i
  have hi := congrArg Subtype.val (congrFun h i)
  have hinv : mixedEmbedding F r⁻¹ * mixedEmbedding F r = 1 := by
    rw [← map_mul (mixedEmbedding F), inv_mul_cancel₀ hr, map_one]
  have hh := congrArg (fun t => mixedEmbedding F r⁻¹ * t) hi
  simpa only [e, ← mul_assoc, hinv, one_mul] using hh

theorem ThetaTest.Construction.rational_mem_mixedPositionLattice (r : F) (q : Fin N → F)
    (h : ∀ i, algebraMap F (ArchimedeanAdeles.Construction.FiniteAdeles F) (r * q i) ∈ IntegralAdeles.Construction.finiteIntegralRing F) :
    ThetaTest.Construction.mixedRationalPosition F N q ∈ ThetaTest.Construction.mixedPositionLattice F N r := by
  intro i
  obtain ⟨b, hb⟩ := (IntegralAdeles.Construction.rational_mem_finiteIntegral_iff F (r * q i)).mp (h i)
  refine ⟨b, ?_⟩
  change mixedEmbedding F (algebraMap (𝓞 F) F b) = mixedEmbedding F r * mixedEmbedding F (q i)
  rw [hb, map_mul (mixedEmbedding F)]

theorem RestrictedTestFamilies.Construction.RestrictedTestFamily.rational_support_lattice (f : RestrictedTestFamilies.Construction.RestrictedTestFamily F N) :
    ∃ r : F, r ≠ 0 ∧ ∀ q : Fin N → F, f.finiteValue F N (FiniteCosets.Construction.finiteRationalPosition q) ≠ 0 →
      ThetaTest.Construction.mixedRationalPosition F N q ∈ ThetaTest.Construction.mixedPositionLattice F N r := by
  obtain ⟨r, hr, hb⟩ := f.finiteValue_denominator F N
  refine ⟨algebraMap (𝓞 F) F r,
    (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 F) F)).mpr hr, fun q hq => ?_⟩
  apply ThetaTest.Construction.rational_mem_mixedPositionLattice F N
  intro i
  have hi := hb (FiniteCosets.Construction.finiteRationalPosition q) hq i
  simpa only [FiniteCosets.Construction.finiteRationalPosition, map_mul, IsScalarTower.algebraMap_apply] using! hi

end

section

/-! Absolute convergence of the actual rational theta sum of every
restricted Bruhat test family over the given number field. -/

open scoped Classical _root_.NumberField
open _root_.NumberField

open OAI.RepresentationTheory.Weil.AdelicSplitting.RapidFunctions.LocalAnalysis

variable (F : Type) [Field F] [NumberField F] (N : ℕ)

theorem RestrictedTestFamilies.Construction.RestrictedTestFamily.theta_norm_summable (f : RestrictedTestFamilies.Construction.RestrictedTestFamily F N) :
    Summable (fun q : Fin N → F => ‖f.value F N (fun i => algebraMap F (ArchimedeanAdeles.Construction.Adeles F) (q i))‖) := by
  obtain ⟨r, hr, hsupport⟩ := f.rational_support_lattice F N
  let L := ThetaTest.Construction.mixedPositionLattice F N r
  let : DiscreteTopology L := ThetaTest.Construction.mixedPositionLattice_discrete F N r hr
  have hf : Summable (fun y : L => ‖f.mixedProductRapid F N y.val‖) := by
    simpa only [zero_add] using RapidFunctions.LocalAnalysis.rapid_lattice_summable_norm L (f.mixedProductRapid F N) 0
  let S : Set (Fin N → F) := {q | f.finiteValue F N (FiniteCosets.Construction.finiteRationalPosition q) ≠ 0}
  let e : S → L := fun q => ⟨ThetaTest.Construction.mixedRationalPosition F N q.val, hsupport q.val q.property⟩
  have he : Function.Injective e := by
    intro q t h
    apply Subtype.ext
    exact ThetaTest.Construction.mixedRationalPosition_injective F N (congrArg Subtype.val h)
  apply (summable_subtype_and_compl (s := S)).mp
  constructor
  · obtain ⟨C, hC⟩ := (f.finiteValue_compactSupport F N).exists_bound_of_continuous
      (f.finiteValue_locallyConstant F N).continuous
    apply ((hf.comp_injective he).mul_right C).of_nonneg_of_le (fun _ => norm_nonneg _)
    intro q
    rw [f.value_rational_factorization F N, norm_mul]
    exact mul_le_mul_of_nonneg_left (hC _) (norm_nonneg _)
  · have hz : (fun q : ↥(Sᶜ) =>
        ‖f.value F N (fun i => algebraMap F (ArchimedeanAdeles.Construction.Adeles F) (q.val i))‖) = 0 := by
      funext q
      have hzero : f.finiteValue F N (FiniteCosets.Construction.finiteRationalPosition q.val) = 0 := by
        simpa only [S, Set.mem_compl_iff, Set.mem_ofPred_eq, not_not] using q.property
      simp only [f.value_rational_factorization F N, hzero, mul_zero, norm_zero, Pi.zero_apply]
    rw [hz]
    exact summable_zero

theorem RestrictedTestFamilies.Construction.RestrictedTestFamily.theta_summable (f : RestrictedTestFamilies.Construction.RestrictedTestFamily F N) :
    Summable (fun q : Fin N → F => f.value F N (fun i => algebraMap F (ArchimedeanAdeles.Construction.Adeles F) (q i))) :=
  (f.theta_norm_summable F N).of_norm

end

/-! Rational Levi generators act on theta by an actual positive real
factor. The factor is a finite product, forced by the vacuum tail. -/

open scoped Classical _root_.NumberField
open Filter

open OAI.RepresentationTheory.Weil.AdelicSplitting.RapidFunctions.LocalAnalysis

variable (F : Type) [Field F] [NumberField F] (N : ℕ)

def ThetaTest.Construction.rationalLeviCoefficient (A : Local.FunctionsMetaplectic.Construction.GeneralLinear F N) (v : ArchimedeanAdeles.Construction.Places F) : ℝ :=
  (Real.sqrt (Local.FunctionsMetaplectic.Construction.localModulus (ArchimedeanAdeles.Construction.Completion F v)
    (Local.FunctionsMetaplectic.Construction.determinantUnit (ArchimedeanAdeles.Construction.Completion F v) (Rational.Construction.localizeLinear F N A v))))⁻¹

theorem ThetaTest.Construction.rationalLeviCoefficient_pos (A : Local.FunctionsMetaplectic.Construction.GeneralLinear F N) (v : ArchimedeanAdeles.Construction.Places F) :
    0 < ThetaTest.Construction.rationalLeviCoefficient F N A v :=
  inv_pos.mpr (Real.sqrt_pos.mpr (Local.FunctionsMetaplectic.Construction.localModulus_pos (ArchimedeanAdeles.Construction.Completion F v) _))

theorem ThetaTest.Construction.localizeLinear_inverse_mulVec (A : Local.FunctionsMetaplectic.Construction.GeneralLinear F N) (q : Fin N → F) (v : ArchimedeanAdeles.Construction.Places F) :
    ((Rational.Construction.localizeLinear F N A v)⁻¹).val.mulVec (fun i => ArchimedeanAdeles.Construction.rationalScalar F v (q i)) =
      fun i => ArchimedeanAdeles.Construction.rationalScalar F v ((A⁻¹).val.mulVec q i) := by
  change ((Units.map (ArchimedeanAdeles.Construction.rationalScalar F v).mapMatrix.toMonoidHom A)⁻¹).val.mulVec _ = _
  rw [← map_inv]
  funext i
  exact (RingHom.map_mulVec (ArchimedeanAdeles.Construction.rationalScalar F v) (A⁻¹).val q i).symm

variable (ψ : AddChar (ArchimedeanAdeles.Construction.Adeles F) ℂ)

theorem ThetaTest.Construction.rationalLeviCoefficient_eventually_one (A : Local.FunctionsMetaplectic.Construction.GeneralLinear F N)
    (a : Rational.Construction.RestrictedCover F N ψ) (ha : Rational.Construction.IsRationalLevi F N ψ A a) :
    ∀ᶠ v : ArchimedeanAdeles.Construction.Places F in cofinite, ThetaTest.Construction.rationalLeviCoefficient F N A v = 1 := by
  have hi : ∀ᶠ v : ArchimedeanAdeles.Construction.Places F in cofinite,
      v ∉ Set.range (Sum.inl : NumberField.InfinitePlace F → ArchimedeanAdeles.Construction.Places F) :=
    (Set.finite_range (Sum.inl : NumberField.InfinitePlace F → ArchimedeanAdeles.Construction.Places F)).compl_mem_cofinite
  filter_upwards [a.property, hi] with v hv harch
  cases v with
  | inl v => exact (harch ⟨v, rfl⟩).elim
  | inr v =>
      let : MeasurableSpace (v.adicCompletion F) := ArchimedeanAdeles.Construction.completionMeasurableSpace F (.inr v)
      let : BorelSpace (v.adicCompletion F) := ArchimedeanAdeles.Construction.completionBorelSpace F (.inr v)
      have hfix := congrArg (fun g : Local.FunctionsMetaplectic.Construction.schwartzBruhat (ArchimedeanAdeles.Construction.Completion F (.inr v)) N => g.val 0) hv.2
      change (Oscillator.Construction.localOperator (ArchimedeanAdeles.Construction.Completion F (.inr v)) N (Characters.Construction.localAdditiveCharacter F ψ (.inr v))
        (a (.inr v)) (Vacuum.Construction.finiteVacuum F N v)).val 0 = (Vacuum.Construction.finiteVacuum F N v).val 0 at hfix
      rw [ha.2] at hfix
      simp only [Local.FunctionsMetaplectic.Construction.substitutionOperator_apply, Matrix.mulVec_zero, Vacuum.Construction.finiteVacuum_zero, mul_one] at hfix
      exact_mod_cast hfix

theorem ThetaTest.Construction.rationalLeviCoefficient_positive_product (A : Local.FunctionsMetaplectic.Construction.GeneralLinear F N)
    (a : Rational.Construction.RestrictedCover F N ψ) (ha : Rational.Construction.IsRationalLevi F N ψ A a) :
    ∃ c : ℝ, 0 < c ∧ HasProd (fun v => (ThetaTest.Construction.rationalLeviCoefficient F N A v : ℂ)) (c : ℂ) := by
  let hs := eventually_cofinite.mp (ThetaTest.Construction.rationalLeviCoefficient_eventually_one F N ψ A a ha)
  let s := hs.toFinset
  have ht : ∀ v ∉ s, ThetaTest.Construction.rationalLeviCoefficient F N A v = 1 := by
    intro v hv
    simpa [s] using hv
  refine ⟨∏ v ∈ s, ThetaTest.Construction.rationalLeviCoefficient F N A v,
    Finset.prod_pos (fun v _ => ThetaTest.Construction.rationalLeviCoefficient_pos F N A v), ?_⟩
  exact (hasProd_prod_of_ne_finset_one ht).map Complex.ofRealHom Complex.continuous_ofReal

theorem RestrictedTestFamilies.Construction.RestrictedTestFamily.levi_rational_value (A : Local.FunctionsMetaplectic.Construction.GeneralLinear F N)
    (a : Rational.Construction.RestrictedCover F N ψ) (ha : Rational.Construction.IsRationalLevi F N ψ A a)
    (c : ℝ) (hc : HasProd (fun v => (ThetaTest.Construction.rationalLeviCoefficient F N A v : ℂ)) (c : ℂ))
    (f : RestrictedTestFamilies.Construction.RestrictedTestFamily F N) (q : Fin N → F) :
    (f.act F N ψ a).value F N (fun i => algebraMap F (ArchimedeanAdeles.Construction.Adeles F) (q i)) =
      (c : ℂ) * f.value F N (fun i => algebraMap F (ArchimedeanAdeles.Construction.Adeles F) ((A⁻¹).val.mulVec q i)) := by
  have hv (v : ArchimedeanAdeles.Construction.Places F) :
      (f.act F N ψ a).localValue F N (fun i => algebraMap F (ArchimedeanAdeles.Construction.Adeles F) (q i)) v =
        (ThetaTest.Construction.rationalLeviCoefficient F N A v : ℂ) * f.localValue F N
          (fun i => algebraMap F (ArchimedeanAdeles.Construction.Adeles F) ((A⁻¹).val.mulVec q i)) v := by
    change (Oscillator.Construction.localOperator (ArchimedeanAdeles.Construction.Completion F v) N (Characters.Construction.localAdditiveCharacter F ψ v) (a v) (f v)).val
      (fun i => ArchimedeanAdeles.Construction.rationalScalar F v (q i)) = _
    rw [ha.2, Local.FunctionsMetaplectic.Construction.substitutionOperator_apply, ThetaTest.Construction.localizeLinear_inverse_mulVec]
    rw [ThetaTest.Construction.rationalLeviCoefficient, Complex.ofReal_inv]
    rfl
  exact ((f.act F N ψ a).localValue_hasProd F N _).unique
    ((hc.mul (f.localValue_hasProd F N _)).congr_fun hv)

theorem ThetaTest.Construction.theta_rational_levi_positive (A : Local.FunctionsMetaplectic.Construction.GeneralLinear F N)
    (a : Rational.Construction.RestrictedCover F N ψ) (ha : Rational.Construction.IsRationalLevi F N ψ A a) :
    ∃ c : ℝ, 0 < c ∧ ∀ f : RestrictedTestFamilies.Construction.RestrictedTestFamily F N,
      (f.act F N ψ a).theta F N = (c : ℂ) * f.theta F N := by
  obtain ⟨c, hc, hp⟩ := ThetaTest.Construction.rationalLeviCoefficient_positive_product F N ψ A a ha
  refine ⟨c, hc, fun f => ?_⟩
  change (∑' q : Fin N → F, (f.act F N ψ a).value F N
      (fun i => algebraMap F (ArchimedeanAdeles.Construction.Adeles F) (q i))) = (c : ℂ) * f.theta F N
  simp_rw [f.levi_rational_value F N ψ A a ha c hp]
  rw [tsum_mul_left]
  congr 1
  exact (LinearSubstitution.LocalAnalysis.positionLinearEquiv A⁻¹).toEquiv.tsum_eq
    (fun q => f.value F N (fun i => algebraMap F (ArchimedeanAdeles.Construction.Adeles F) (q i)))

end

end OAI.RepresentationTheory.Weil.AdelicSplitting
