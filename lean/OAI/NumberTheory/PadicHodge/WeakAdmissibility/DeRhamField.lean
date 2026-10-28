import OAI.NumberTheory.PadicHodge.WeakAdmissibility.PeriodUniformizer
import OAI.NumberTheory.PadicHodge.WeakAdmissibility.ComparisonScalars

/-! # De Rham Field -/

namespace OAI

noncomputable section

namespace NumberTheory.PadicHodge.WeakAdmissibility.DeRhamField.Filtration

/-! The exhaustive, separated integer filtration on the actual de Rham field. -/

open OAI.NumberTheory.PadicHodge.WeakAdmissibility.Logarithm.PeriodRings OAI.NumberTheory.PadicHodge.WeakAdmissibility.DeRham OAI.NumberTheory.PadicHodge.WeakAdmissibility.DeRhamDVR OAI.NumberTheory.PadicHodge.WeakAdmissibility.ComparisonBd OAI.NumberTheory.PadicHodge.WeakAdmissibility.Comparison
open OAI.NumberTheory.PadicHodge.WeakAdmissibility.PeriodUniformizer OAI.NumberTheory.PadicHodge.WeakAdmissibility.ComparisonScalars
variable (p : ℕ) [Fact p.Prime]

def tPlus : DeRhamDVR.DeRhamCompletion p := Comparison.aCrisToBdRPlus p (Logarithm.PeriodRings.cyclotomicPeriod p)

def tField : Logarithm.PeriodRings.BdR p := algebraMap (DeRhamDVR.DeRhamCompletion p) (Logarithm.PeriodRings.BdR p) (tPlus p)

theorem tPlus_ne_zero : tPlus p ≠ 0 := DeRhamLog.cyclotomicPeriod_deRham_ne_zero p

theorem tField_ne_zero : tField p ≠ 0 :=
  (map_ne_zero_iff _ (ComparisonBd.deRham_algebraMap_injective p)).mpr (tPlus_ne_zero p)

instance tPlus_complete : IsAdicComplete (Ideal.span {tPlus p}) (DeRhamDVR.DeRhamCompletion p) := by
  have he : Ideal.span {DeRhamDVR.xiDeRham p} = Ideal.span {tPlus p} :=
    Ideal.span_singleton_eq_span_singleton.mpr (PeriodUniformizer.associated_xi_cyclotomicPeriod p)
  exact he ▸ DeRhamDVR.completion_complete p

instance completion_padicAlgebra : Algebra ℚ_[p] (DeRhamDVR.DeRhamCompletion p) := (ComparisonScalars.padicToBdRPlus p).toAlgebra

instance completion_padicModule : Module ℚ_[p] (DeRhamDVR.DeRhamCompletion p) := Algebra.toModule

instance completion_scalarTower : IsScalarTower ℚ_[p] (DeRhamDVR.DeRhamCompletion p) (Logarithm.PeriodRings.BdR p) :=
  IsScalarTower.of_algebraMap_eq (fun _ => rfl)

/-- Fil^i B_dR = t^i B_dR^+, retaining the integral coefficient module. -/
def filtration (i : ℤ) : Submodule (DeRhamDVR.DeRhamCompletion p) (Logarithm.PeriodRings.BdR p) :=
  Submodule.span (DeRhamDVR.DeRhamCompletion p) {tField p ^ i}

theorem mem_filtration (i : ℤ) (x : Logarithm.PeriodRings.BdR p) : x ∈ filtration p i ↔
    ∃ a : DeRhamDVR.DeRhamCompletion p, algebraMap (DeRhamDVR.DeRhamCompletion p) (Logarithm.PeriodRings.BdR p) a * tField p ^ i = x := by
  rw [filtration, Submodule.mem_span_singleton]
  simp only [Algebra.smul_def]

theorem filtration_antitone : Antitone (filtration p) := by
  intro i j hij x hx
  obtain ⟨a, ha⟩ := (mem_filtration p j x).mp hx
  let n : ℕ := (j - i).toNat
  have hn : (n : ℤ) = j - i := Int.toNat_of_nonneg (sub_nonneg.mpr hij)
  apply (mem_filtration p i x).mpr
  refine ⟨a * tPlus p ^ n, ?_⟩
  calc
    algebraMap (DeRhamDVR.DeRhamCompletion p) (Logarithm.PeriodRings.BdR p) (a * tPlus p ^ n) * tField p ^ i =
        algebraMap (DeRhamDVR.DeRhamCompletion p) (Logarithm.PeriodRings.BdR p) a * (tField p ^ (n : ℤ) * tField p ^ i) := by
          rw [map_mul, map_pow, zpow_natCast, mul_assoc]
          rfl
    _ = algebraMap (DeRhamDVR.DeRhamCompletion p) (Logarithm.PeriodRings.BdR p) a * tField p ^ ((n : ℤ) + i) := by
      rw [← zpow_add₀ (tField_ne_zero p)]
    _ = x := by rw [hn, sub_add_cancel, ha]

theorem filtration_mul (i j : ℤ) {x y : Logarithm.PeriodRings.BdR p}
    (hx : x ∈ filtration p i) (hy : y ∈ filtration p j) : x * y ∈ filtration p (i + j) := by
  obtain ⟨a, rfl⟩ := (mem_filtration p i x).mp hx
  obtain ⟨b, rfl⟩ := (mem_filtration p j y).mp hy
  apply (mem_filtration p (i + j) _).mpr
  refine ⟨a * b, ?_⟩
  rw [map_mul, zpow_add₀ (tField_ne_zero p)]
  ring

theorem filtration_exhaustive (x : Logarithm.PeriodRings.BdR p) : ∃ i : ℤ, x ∈ filtration p i := by
  by_cases hx : x = 0
  · exact ⟨0, hx ▸ (filtration p 0).zero_mem⟩
  obtain ⟨i, u, hu⟩ := IsDiscreteValuationRing.exists_units_eq_smul_zpow_of_irreducible
    (R := DeRhamDVR.DeRhamCompletion p) (K := Logarithm.PeriodRings.BdR p) (ϖ := tPlus p) (PeriodUniformizer.cyclotomicPeriod_irreducible p) hx
  refine ⟨i, (mem_filtration p i x).mpr ⟨u, ?_⟩⟩
  simpa only [Units.smul_def, Algebra.smul_def, tField] using hu.symm

theorem filtration_zero (x : Logarithm.PeriodRings.BdR p) : x ∈ filtration p 0 ↔
    ∃ a : DeRhamDVR.DeRhamCompletion p, algebraMap (DeRhamDVR.DeRhamCompletion p) (Logarithm.PeriodRings.BdR p) a = x := by
  rw [mem_filtration]
  simp only [zpow_zero, mul_one]

theorem filtration_separated (x : Logarithm.PeriodRings.BdR p) (hx : ∀ i : ℤ, x ∈ filtration p i) : x = 0 := by
  obtain ⟨a, ha⟩ := (filtration_zero p x).mp (hx 0)
  have ha₀ : a = 0 := by
    apply IsHausdorff.haus (show IsHausdorff (Ideal.span {tPlus p}) (DeRhamDVR.DeRhamCompletion p) from inferInstance)
    intro n
    rw [SModEq.sub_mem, sub_zero, smul_eq_mul, Ideal.mul_top,
      Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    obtain ⟨b, hb⟩ := (mem_filtration p (n : ℤ) x).mp (hx n)
    refine ⟨b, ?_⟩
    apply ComparisonBd.deRham_algebraMap_injective p
    rw [map_mul, map_pow, ha]
    change x = tField p ^ n * algebraMap (DeRhamDVR.DeRhamCompletion p) (Logarithm.PeriodRings.BdR p) b
    rw [← hb, zpow_natCast, mul_comm]
  rw [← ha, ha₀, map_zero]

theorem tField_mem_one : tField p ∈ filtration p 1 := by
  apply (mem_filtration p 1 _).mpr
  exact ⟨1, by rw [map_one, one_mul, zpow_one]⟩

theorem tField_not_mem_two : tField p ∉ filtration p 2 := by
  intro hx
  obtain ⟨a, ha⟩ := (mem_filtration p 2 _).mp hx
  have he : tPlus p ^ 2 * a = tPlus p := by
    apply ComparisonBd.deRham_algebraMap_injective p
    rw [map_mul, map_pow]
    change tField p ^ 2 * algebraMap (DeRhamDVR.DeRhamCompletion p) (Logarithm.PeriodRings.BdR p) a = tField p
    simpa only [zpow_ofNat, mul_comm] using ha
  have hone : tPlus p * a = 1 := by
    apply mul_left_cancel₀ (tPlus_ne_zero p)
    rw [← mul_assoc, ← pow_two, he, mul_one]
  exact (PeriodUniformizer.cyclotomicPeriod_irreducible p).not_isUnit (IsUnit.of_mul_eq_one _ hone)

/-- The same canonical filtration as a Q_p-subspace filtration. -/
def rationalFiltration (i : ℤ) : Submodule ℚ_[p] (Logarithm.PeriodRings.BdR p) := (filtration p i).restrictScalars ℚ_[p]

theorem rationalFiltration_antitone : Antitone (rationalFiltration p) := filtration_antitone p

end NumberTheory.PadicHodge.WeakAdmissibility.DeRhamField.Filtration

namespace NumberTheory.PadicHodge.WeakAdmissibility.DeRhamField.Constants

/-! Canonical scalar reduction and rigidity of algebraic de Rham constants. -/

open OAI.NumberTheory.PadicHodge.WeakAdmissibility.Logarithm.PeriodRings OAI.NumberTheory.PadicHodge.WeakAdmissibility.DeRham OAI.NumberTheory.PadicHodge.WeakAdmissibility.DeRhamEmbedding.Residue OAI.NumberTheory.PadicHodge.WeakAdmissibility.DeRhamDVR OAI.NumberTheory.PadicHodge.WeakAdmissibility.ComparisonScalars
open OAI.NumberTheory.PadicHodge.WeakAdmissibility.DeRhamField.Filtration
variable (p : ℕ) [Fact p.Prime]

theorem padicInt_ringHom_unique {R : Type*} [CommRing R]
    [IsHausdorff (Ideal.span {(p : R)}) R] (f g : ℤ_[p] →+* R) : f = g := by
  apply RingHom.ext
  intro a
  apply sub_eq_zero.mp
  apply IsHausdorff.haus (show IsHausdorff (Ideal.span {(p : R)}) R from inferInstance)
  intro n
  rw [SModEq.sub_mem, sub_zero, smul_eq_mul, Ideal.mul_top,
    Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  have hd : a - ((a.toZModPow n).val : ℤ_[p]) ∈ Ideal.span {(p : ℤ_[p]) ^ n} := by
    rw [← PadicInt.ker_toZModPow, RingHom.mem_ker]
    simp only [map_sub, map_natCast, ZMod.natCast_zmod_val, sub_self]
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp hd
  have hf := congrArg f hc
  have hg := congrArg g hc
  simp only [map_sub, map_natCast, map_mul, map_pow] at hf hg
  refine ⟨f c - g c, ?_⟩
  linear_combination hf - hg

def padicIntegerToIntegers : ℤ_[p] →+* 𝓞_ℂ_[p] where
  toFun a := ⟨algebraMap ℚ_[p] ℂ_[p] (a : ℚ_[p]), by
    change (Valued.v (algebraMap ℚ_[p] ℂ_[p] (a : ℚ_[p])) : NNReal) ≤ 1
    rw [Logarithm.PeriodRings.valuation_eq_nnnorm]
    have hn : ‖algebraMap ℚ_[p] ℂ_[p] (a : ℚ_[p])‖ ≤ 1 := by
      exact (PadicComplex.norm_extends' p (a : ℚ_[p])).le.trans a.property
    exact_mod_cast hn⟩
  map_zero' := Subtype.ext (by simp)
  map_one' := Subtype.ext (by simp)
  map_add' a b := Subtype.ext (by simp)
  map_mul' a b := Subtype.ext (by simp)

theorem theta_padicIntToAInf (a : ℤ_[p]) :
    Logarithm.PeriodRings.theta p (Logarithm.PeriodRings.padicIntToAInf p a) = padicIntegerToIntegers p a :=
  DFunLike.congr_fun (padicInt_ringHom_unique p ((Logarithm.PeriodRings.theta p).comp (Logarithm.PeriodRings.padicIntToAInf p))
    (padicIntegerToIntegers p)) a

theorem residue_padic (a : ℚ_[p]) :
    DeRhamDVR.residue p (algebraMap ℚ_[p] (DeRhamDVR.DeRhamCompletion p) a) = algebraMap ℚ_[p] ℂ_[p] a := by
  have he : (DeRhamDVR.residue p).comp (algebraMap ℚ_[p] (DeRhamDVR.DeRhamCompletion p)) = algebraMap ℚ_[p] ℂ_[p] := by
    apply IsLocalization.ringHom_ext (nonZeroDivisors ℤ_[p])
    apply RingHom.ext
    intro b
    change DeRhamDVR.residue p (ComparisonScalars.padicToBdRPlus p (algebraMap ℤ_[p] ℚ_[p] b)) =
      algebraMap ℚ_[p] ℂ_[p] (algebraMap ℤ_[p] ℚ_[p] b)
    rw [ComparisonScalars.padicToBdRPlus_integer]
    change DeRhamDVR.residue p (algebraMap (Logarithm.PeriodRings.BInf p) (DeRhamDVR.DeRhamCompletion p)
      (algebraMap (Logarithm.PeriodRings.AInf p) (Logarithm.PeriodRings.BInf p) (Logarithm.PeriodRings.padicIntToAInf p b))) = _
    rw [DeRhamDVR.residue_of, DeRham.bInfTheta_algebraMap, DeRham.integerLocalizationToCp_algebraMap, theta_padicIntToAInf]
    rfl
  exact DFunLike.congr_fun he a

def residueAlg : DeRhamDVR.DeRhamCompletion p →ₐ[ℚ_[p]] ℂ_[p] :=
  { DeRhamDVR.residue p with commutes' := residue_padic p }

/-- Integral constants are uniquely determined by their actual residue. -/
theorem integral_residue_injective {x y : DeRhamDVR.DeRhamCompletion p}
    (hx : IsIntegral ℚ_[p] x) (hy : IsIntegral ℚ_[p] y) (hres : DeRhamDVR.residue p x = DeRhamDVR.residue p y) : x = y := by
  apply sub_eq_zero.mp
  by_contra hxy
  have hu := (hx.sub hy).isUnit hxy
  apply (hu.map (DeRhamDVR.residue p)).ne_zero
  rw [map_sub, hres, sub_self]

theorem exists_integral_lift (a : ℂ_[p]) (ha : IsIntegral ℚ_[p] a) :
    ∃ x : DeRhamDVR.DeRhamCompletion p, IsIntegral ℚ_[p] x ∧ DeRhamDVR.residue p x = a := by
  let I : Ideal (DeRhamDVR.DeRhamCompletion p) := RingHom.ker (DeRhamDVR.residue p)
  let : IsAdicComplete I (DeRhamDVR.DeRhamCompletion p) := by
    dsimp only [I]
    rw [DeRhamDVR.residue_kernel_span]
    infer_instance
  let P : Polynomial ℚ_[p] := minpoly ℚ_[p] a
  let g : Polynomial (DeRhamDVR.DeRhamCompletion p) := P.map (algebraMap ℚ_[p] (DeRhamDVR.DeRhamCompletion p))
  have hP : P.Monic := minpoly.monic ha
  have hsep : P.Separable := (minpoly.irreducible ha).separable
  have hroot : Polynomial.aeval a P = 0 := minpoly.aeval ℚ_[p] a
  obtain ⟨a₀, ha₀⟩ := DeRhamDVR.residue_surjective p a
  have hmap (Q : Polynomial ℚ_[p]) :
      DeRhamDVR.residue p ((Q.map (algebraMap ℚ_[p] (DeRhamDVR.DeRhamCompletion p))).eval a₀) = Polynomial.aeval a Q := by
    rw [Polynomial.eval_map_algebraMap]
    exact (Polynomial.aeval_algHom_apply (residueAlg p) a₀ Q).symm.trans
      (congrArg (fun b : ℂ_[p] => Polynomial.aeval b Q) ha₀)
  have hzero : g.eval a₀ ∈ I := by
    change DeRhamDVR.residue p (g.eval a₀) = 0
    exact (hmap P).trans hroot
  have hder : IsUnit (Ideal.Quotient.mk I (g.derivative.eval a₀)) := by
    apply IsUnit.map
    apply DeRhamDVR.residue_ne_zero_isUnit p
    change DeRhamDVR.residue p ((P.map (algebraMap ℚ_[p] (DeRhamDVR.DeRhamCompletion p))).derivative.eval a₀) ≠ 0
    rw [Polynomial.derivative_map, hmap]
    exact hsep.aeval_derivative_ne_zero hroot
  obtain ⟨x, hx, hx₀⟩ := HenselianRing.is_henselian (I := I) g (hP.map _) a₀ hzero hder
  refine ⟨x, ⟨P, hP, ?_⟩, ?_⟩
  · change Polynomial.aeval x P = 0
    rw [← Polynomial.eval_map_algebraMap]
    exact hx
  · have he : DeRhamDVR.residue p (x - a₀) = 0 := hx₀
    rw [map_sub, ha₀, sub_eq_zero] at he
    exact he

theorem algebraicClosure_integral (a : PadicAlgCl p) :
    IsIntegral ℚ_[p] (algebraMap (PadicAlgCl p) ℂ_[p] a) :=
  (Algebra.IsIntegral.isIntegral (R := ℚ_[p]) a).map
    (IsScalarTower.toAlgHom ℚ_[p] (PadicAlgCl p) ℂ_[p])

def algebraicLift (a : PadicAlgCl p) : DeRhamDVR.DeRhamCompletion p :=
  (exists_integral_lift p (algebraMap (PadicAlgCl p) ℂ_[p] a) (algebraicClosure_integral p a)).choose

theorem algebraicLift_integral (a : PadicAlgCl p) : IsIntegral ℚ_[p] (algebraicLift p a) :=
  (exists_integral_lift p (algebraMap (PadicAlgCl p) ℂ_[p] a) (algebraicClosure_integral p a)).choose_spec.1

theorem algebraicLift_residue (a : PadicAlgCl p) :
    DeRhamDVR.residue p (algebraicLift p a) = algebraMap (PadicAlgCl p) ℂ_[p] a :=
  (exists_integral_lift p (algebraMap (PadicAlgCl p) ℂ_[p] a) (algebraicClosure_integral p a)).choose_spec.2

/-- The canonical embedding of the fixed p-adic algebraic closure, obtained by Hensel lifting. -/
def algebraicToBdRPlus : PadicAlgCl p →ₐ[ℚ_[p]] DeRhamDVR.DeRhamCompletion p where
  toFun := algebraicLift p
  map_zero' := integral_residue_injective p (algebraicLift_integral p 0) isIntegral_zero (by
    rw [algebraicLift_residue, map_zero, map_zero])
  map_one' := integral_residue_injective p (algebraicLift_integral p 1) isIntegral_one (by
    rw [algebraicLift_residue, map_one, map_one])
  map_add' a b := integral_residue_injective p (algebraicLift_integral p (a + b))
    ((algebraicLift_integral p a).add (algebraicLift_integral p b)) (by
      rw [algebraicLift_residue, map_add, map_add, algebraicLift_residue, algebraicLift_residue])
  map_mul' a b := integral_residue_injective p (algebraicLift_integral p (a * b))
    ((algebraicLift_integral p a).mul (algebraicLift_integral p b)) (by
      rw [algebraicLift_residue, map_mul, map_mul, algebraicLift_residue, algebraicLift_residue])
  commutes' a := integral_residue_injective p (algebraicLift_integral p _)
    (isIntegral_algebraMap) (by
      rw [algebraicLift_residue, residue_padic,
        ← IsScalarTower.algebraMap_apply ℚ_[p] (PadicAlgCl p) ℂ_[p] a])

theorem algebraicToBdRPlus_residue (a : PadicAlgCl p) :
    DeRhamDVR.residue p (algebraicToBdRPlus p a) = algebraMap (PadicAlgCl p) ℂ_[p] a := algebraicLift_residue p a

end NumberTheory.PadicHodge.WeakAdmissibility.DeRhamField.Constants

namespace NumberTheory.PadicHodge.WeakAdmissibility.DeRhamField.Scalars

/-! The genuine K-scalar action, obtained from canonical algebraic constants. -/

open OAI.NumberTheory.PadicHodge.WeakAdmissibility.Logarithm.PeriodRings OAI.NumberTheory.PadicHodge.WeakAdmissibility.DeRham OAI.NumberTheory.PadicHodge.WeakAdmissibility.DeRhamDVR OAI.NumberTheory.PadicHodge.WeakAdmissibility.DeRhamEmbedding.Residue OAI.NumberTheory.PadicHodge.WeakAdmissibility.DeRhamField.Constants
open OAI.NumberTheory.PadicHodge.WeakAdmissibility.ComparisonBd OAI.NumberTheory.PadicHodge.WeakAdmissibility.ComparisonGalois OAI.NumberTheory.PadicHodge.WeakAdmissibility.ComparisonScalars OAI.NumberTheory.PadicHodge.WeakAdmissibility.DeRhamField.Filtration
variable (p : ℕ) [Fact p.Prime]

theorem integerLocalizationToCp_galois (σ : PeriodInvariants.PeriodRing.PadicGalois p) (x : DeRham.IntegerLocalization p) :
    DeRham.integerLocalizationToCp p (DeRham.integerLocalizationMap p (PeriodInvariants.PeriodRing.galoisIntegerEquiv p σ).toRingHom x) =
      PeriodInvariants.PeriodRing.galoisComplexEquiv p σ (DeRham.integerLocalizationToCp p x) := by
  have he : (DeRham.integerLocalizationToCp p).comp
      (DeRham.integerLocalizationMap p (PeriodInvariants.PeriodRing.galoisIntegerEquiv p σ).toRingHom) =
      (PeriodInvariants.PeriodRing.galoisComplexEquiv p σ).toRingHom.comp (DeRham.integerLocalizationToCp p) := by
    apply IsLocalization.ringHom_ext (Submonoid.powers (p : 𝓞_ℂ_[p]))
    apply RingHom.ext
    intro a
    simp only [RingHom.comp_apply, DeRham.integerLocalizationMap_algebraMap,
      DeRham.integerLocalizationToCp_algebraMap, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
    rfl
  exact DFunLike.congr_fun he x

theorem residue_galois (σ : PeriodInvariants.PeriodRing.PadicGalois p) (x : DeRhamDVR.DeRhamCompletion p) :
    DeRhamDVR.residue p (ComparisonGalois.completionGaloisAction p σ x) = PeriodInvariants.PeriodRing.galoisComplexEquiv p σ (DeRhamDVR.residue p x) := by
  change DeRham.integerLocalizationToCp p (DeRham.thetaBdRPlus p
    (DeRham.bdRPlusMap p (PeriodInvariants.PeriodRing.galoisIntegerEquiv p σ).toRingHom x)) = _
  erw [DeRham.thetaBdRPlus_natural, integerLocalizationToCp_galois]
  rfl

theorem completionGaloisAction_padic (σ : PeriodInvariants.PeriodRing.PadicGalois p) (a : ℚ_[p]) :
    ComparisonGalois.completionGaloisAction p σ (algebraMap ℚ_[p] (DeRhamDVR.DeRhamCompletion p) a) =
      algebraMap ℚ_[p] (DeRhamDVR.DeRhamCompletion p) a := by
  apply ComparisonBd.deRham_algebraMap_injective p
  change ComparisonBd.bdRPlusToBdR p (DeRham.galoisBdRPlusAction p σ (ComparisonScalars.padicToBdRPlus p a)) =
    ComparisonBd.bdRPlusToBdR p (ComparisonScalars.padicToBdRPlus p a)
  rw [← ComparisonGalois.galoisBdRAction_of]
  exact ComparisonScalars.galoisBdRAction_padic p σ a

def completionGaloisAlgEquiv (σ : PeriodInvariants.PeriodRing.PadicGalois p) :
    DeRhamDVR.DeRhamCompletion p ≃ₐ[ℚ_[p]] DeRhamDVR.DeRhamCompletion p :=
  { ComparisonGalois.completionGaloisAction p σ with commutes' := completionGaloisAction_padic p σ }

theorem galoisComplexEquiv_algebraic (σ : PeriodInvariants.PeriodRing.PadicGalois p) (a : PadicAlgCl p) :
    PeriodInvariants.PeriodRing.galoisComplexEquiv p σ (algebraMap (PadicAlgCl p) ℂ_[p] a) =
      algebraMap (PadicAlgCl p) ℂ_[p] (σ a) := by
  change UniformSpace.Completion.mapRingHom σ.toRingEquiv.toRingHom
    (PeriodInvariants.PeriodRing.algebraicGalois_isometry p σ).continuous a = _
  erw [UniformSpace.Completion.mapRingHom_coe]
  rfl

theorem algebraicToBdRPlus_galois (σ : PeriodInvariants.PeriodRing.PadicGalois p) (a : PadicAlgCl p) :
    ComparisonGalois.completionGaloisAction p σ (Constants.algebraicToBdRPlus p a) = Constants.algebraicToBdRPlus p (σ a) := by
  apply Constants.integral_residue_injective p
    ((Constants.algebraicLift_integral p a).map (completionGaloisAlgEquiv p σ).toAlgHom)
    (Constants.algebraicLift_integral p (σ a))
  change DeRhamDVR.residue p (ComparisonGalois.completionGaloisAction p σ (Constants.algebraicToBdRPlus p a)) =
    DeRhamDVR.residue p (Constants.algebraicToBdRPlus p (σ a))
  rw [residue_galois, Constants.algebraicToBdRPlus_residue, Constants.algebraicToBdRPlus_residue, galoisComplexEquiv_algebraic]

variable (K : IntermediateField ℚ_[p] (PadicAlgCl p))

/-- The canonical K → B_dR^+ scalar embedding. -/
def fieldToCompletion : K →ₐ[ℚ_[p]] DeRhamDVR.DeRhamCompletion p := (Constants.algebraicToBdRPlus p).comp K.val

instance completion_fieldAlgebra : Algebra K (DeRhamDVR.DeRhamCompletion p) := (fieldToCompletion p K).toRingHom.toAlgebra

instance completion_fieldSMul : SMul K (DeRhamDVR.DeRhamCompletion p) :=
  ⟨fun a x => fieldToCompletion p K a * x⟩

instance completion_fieldModule : Module K (DeRhamDVR.DeRhamCompletion p) := Algebra.toModule

instance completion_fieldScalarTower : IsScalarTower ℚ_[p] K (DeRhamDVR.DeRhamCompletion p) :=
  IsScalarTower.of_algebraMap_eq (R := ℚ_[p]) (S := K) (A := DeRhamDVR.DeRhamCompletion p)
    (fun a => ((fieldToCompletion p K).commutes a).symm)

def fieldToDeRham : K →ₐ[ℚ_[p]] Logarithm.PeriodRings.BdR p :=
  (IsScalarTower.toAlgHom ℚ_[p] (DeRhamDVR.DeRhamCompletion p) (Logarithm.PeriodRings.BdR p)).comp (fieldToCompletion p K)

instance deRham_fieldAlgebra : Algebra K (Logarithm.PeriodRings.BdR p) := (fieldToDeRham p K).toRingHom.toAlgebra

instance deRham_fieldModule : Module K (Logarithm.PeriodRings.BdR p) := Algebra.toModule

instance deRham_fieldScalarTower : IsScalarTower ℚ_[p] K (Logarithm.PeriodRings.BdR p) :=
  IsScalarTower.of_algebraMap_eq (fun a => ((fieldToDeRham p K).commutes a).symm)

instance field_completion_scalarTower : IsScalarTower K (DeRhamDVR.DeRhamCompletion p) (Logarithm.PeriodRings.BdR p) :=
  IsScalarTower.of_algebraMap_eq (fun _ => rfl)

theorem completionGaloisAction_field (σ : K.fixingSubgroup) (a : K) :
    ComparisonGalois.completionGaloisAction p σ.val (algebraMap K (DeRhamDVR.DeRhamCompletion p) a) =
      algebraMap K (DeRhamDVR.DeRhamCompletion p) a := by
  change ComparisonGalois.completionGaloisAction p σ.val (Constants.algebraicToBdRPlus p (a : PadicAlgCl p)) =
    Constants.algebraicToBdRPlus p (a : PadicAlgCl p)
  rw [algebraicToBdRPlus_galois]
  exact congrArg (Constants.algebraicToBdRPlus p) (σ.property a)

theorem galoisBdRAction_field (σ : K.fixingSubgroup) (a : K) :
    ComparisonGalois.galoisBdRAction p σ.val (algebraMap K (Logarithm.PeriodRings.BdR p) a) = algebraMap K (Logarithm.PeriodRings.BdR p) a := by
  change ComparisonGalois.galoisBdRAction p σ.val (ComparisonBd.bdRPlusToBdR p (fieldToCompletion p K a)) =
    ComparisonBd.bdRPlusToBdR p (fieldToCompletion p K a)
  erw [ComparisonGalois.galoisBdRAction_of]
  exact congrArg (ComparisonBd.bdRPlusToBdR p) (completionGaloisAction_field p K σ a)

def galoisBdRFieldAlgEquiv (σ : K.fixingSubgroup) : Logarithm.PeriodRings.BdR p ≃ₐ[K] Logarithm.PeriodRings.BdR p :=
  { ComparisonGalois.galoisBdRAction p σ.val with commutes' := galoisBdRAction_field p K σ }

def fieldFiltration (i : ℤ) : Submodule K (Logarithm.PeriodRings.BdR p) := (Filtration.filtration p i).restrictScalars K

theorem fieldFiltration_antitone : Antitone (fieldFiltration p K) := Filtration.filtration_antitone p

end NumberTheory.PadicHodge.WeakAdmissibility.DeRhamField.Scalars

end

end OAI
