import OAI.NumberTheory.PadicHodge.WeakAdmissibility.Cyclotomic

/-! # Galois -/

namespace OAI

noncomputable section

namespace NumberTheory.PadicHodge.WeakAdmissibility.Galois

/-!
Galois maps on the actual crystalline period rings, including the extension
past the cyclotomic period justified by its proved transformation formula.
-/

open OAI.NumberTheory.PadicHodge.WeakAdmissibility.Logarithm.PeriodRings OAI.NumberTheory.PadicHodge.WeakAdmissibility.Cyclotomic

variable (p : ℕ) [Fact p.Prime]

theorem thetaModP_natural (f : 𝓞_ℂ_[p] →+* 𝓞_ℂ_[p]) (x : Logarithm.PeriodRings.AInf p) :
    Logarithm.PeriodRings.thetaModP p (PeriodInvariants.PeriodRing.ainfMap p f x) = PeriodInvariants.PeriodRing.modPMap p f (Logarithm.PeriodRings.thetaModP p x) := by
  change Ideal.Quotient.mk _ (Logarithm.PeriodRings.theta p (PeriodInvariants.PeriodRing.ainfMap p f x)) =
    PeriodInvariants.PeriodRing.modPMap p f (Ideal.Quotient.mk _ (Logarithm.PeriodRings.theta p x))
  rw [PeriodInvariants.PeriodRing.modPMap_mk]
  congr 1
  exact PeriodInvariants.PeriodRing.theta_natural p f x

theorem transformed_kernel (f : 𝓞_ℂ_[p] ≃+* 𝓞_ℂ_[p]) (x : Logarithm.PeriodRings.AInf p)
    (hx : Logarithm.PeriodRings.thetaModP p x = 0) : Logarithm.PeriodRings.thetaModP p (PeriodInvariants.PeriodRing.ainfEquiv p f x) = 0 := by
  change Logarithm.PeriodRings.thetaModP p (PeriodInvariants.PeriodRing.ainfMap p f.toRingHom x) = 0
  rw [thetaModP_natural, hx, map_zero]

theorem fractionMap_preserves_envelope (f : 𝓞_ℂ_[p] ≃+* 𝓞_ℂ_[p])
    {x : Logarithm.PeriodRings.AInfFractionField p} (hx : x ∈ Logarithm.PeriodRings.aCrisUncompleted p) :
    PeriodInvariants.PeriodRing.ainfFractionEquiv p f x ∈ Logarithm.PeriodRings.aCrisUncompleted p := by
  induction hx using Algebra.adjoin_induction with
  | mem z hz =>
    obtain ⟨x, n, hx, rfl⟩ := hz
    rw [map_div₀, map_pow, map_natCast, PeriodInvariants.PeriodRing.ainfFractionEquiv_algebraMap]
    exact Logarithm.PeriodRings.dividedPower_mem p _ n (transformed_kernel p f x hx)
  | algebraMap r =>
    rw [PeriodInvariants.PeriodRing.ainfFractionEquiv_algebraMap]
    exact (Logarithm.PeriodRings.aCrisUncompleted p).algebraMap_mem _
  | add x y _ _ hx hy =>
    rw [map_add]
    exact (Logarithm.PeriodRings.aCrisUncompleted p).add_mem hx hy
  | mul x y _ _ hx hy =>
    rw [map_mul]
    exact (Logarithm.PeriodRings.aCrisUncompleted p).mul_mem hx hy

def uncompletedMap (f : 𝓞_ℂ_[p] ≃+* 𝓞_ℂ_[p]) : Logarithm.PeriodRings.ACrisUncompleted p →+* Logarithm.PeriodRings.ACrisUncompleted p where
  toFun x := ⟨PeriodInvariants.PeriodRing.ainfFractionEquiv p f x, fractionMap_preserves_envelope p f x.property⟩
  map_zero' := Subtype.ext (map_zero _)
  map_one' := Subtype.ext (map_one _)
  map_add' x y := Subtype.ext (map_add (PeriodInvariants.PeriodRing.ainfFractionEquiv p f)
    (x : Logarithm.PeriodRings.AInfFractionField p) (y : Logarithm.PeriodRings.AInfFractionField p))
  map_mul' x y := Subtype.ext (map_mul (PeriodInvariants.PeriodRing.ainfFractionEquiv p f)
    (x : Logarithm.PeriodRings.AInfFractionField p) (y : Logarithm.PeriodRings.AInfFractionField p))

theorem uncompletedMap_dividedPower (f : 𝓞_ℂ_[p] ≃+* 𝓞_ℂ_[p]) (x : Logarithm.PeriodRings.AInf p)
    (hx : Logarithm.PeriodRings.thetaModP p x = 0) (n : ℕ) :
    uncompletedMap p f (Logarithm.PeriodRings.dividedPower p x n hx) =
      Logarithm.PeriodRings.dividedPower p (PeriodInvariants.PeriodRing.ainfEquiv p f x) n (transformed_kernel p f x hx) := by
  apply Subtype.ext
  change PeriodInvariants.PeriodRing.ainfFractionEquiv p f
    (algebraMap (Logarithm.PeriodRings.AInf p) (Logarithm.PeriodRings.AInfFractionField p) x ^ n / (n.factorial : Logarithm.PeriodRings.AInfFractionField p)) = _
  rw [map_div₀, map_pow, map_natCast, PeriodInvariants.PeriodRing.ainfFractionEquiv_algebraMap]
  rfl

theorem uncompletedMap_logTerm (f : 𝓞_ℂ_[p] ≃+* 𝓞_ℂ_[p]) (x : Logarithm.PeriodRings.AInf p)
    (hx : Logarithm.PeriodRings.thetaModP p x = 0) (n : ℕ) :
    uncompletedMap p f (Logarithm.PeriodRings.crystallineLogTerm p x hx n) =
      Logarithm.PeriodRings.crystallineLogTerm p (PeriodInvariants.PeriodRing.ainfEquiv p f x) (transformed_kernel p f x hx) n := by
  simp only [Logarithm.PeriodRings.crystallineLogTerm, map_mul, map_pow, map_neg, map_one, map_natCast,
    uncompletedMap_dividedPower]

theorem uncompletedMap_preserves_p (f : 𝓞_ℂ_[p] ≃+* 𝓞_ℂ_[p]) :
    (Ideal.span {(p : Logarithm.PeriodRings.ACrisUncompleted p)}).map (uncompletedMap p f) ≤
      Ideal.span {(p : Logarithm.PeriodRings.ACrisUncompleted p)} := by
  rw [Ideal.map_span]
  simp

def completedMap (f : 𝓞_ℂ_[p] ≃+* 𝓞_ℂ_[p]) : Logarithm.PeriodRings.ACris p →+* Logarithm.PeriodRings.ACris p :=
  Logarithm.PeriodRings.completionMap (Ideal.span {(p : Logarithm.PeriodRings.ACrisUncompleted p)}) (uncompletedMap p f)
    (uncompletedMap_preserves_p p f)

theorem completedMap_log (f : 𝓞_ℂ_[p] ≃+* 𝓞_ℂ_[p]) (x : Logarithm.PeriodRings.AInf p)
    (hx : Logarithm.PeriodRings.thetaModP p x = 0) :
    completedMap p f (Logarithm.PeriodRings.crystallineLog p x hx) =
      Logarithm.PeriodRings.crystallineLog p (PeriodInvariants.PeriodRing.ainfEquiv p f x) (transformed_kernel p f x hx) := by
  apply AdicCompletion.ext_evalₐ
  intro k
  rw [completedMap, Logarithm.PeriodRings.completionMap, AdicCompletion.evalₐ_liftRingHom]
  simp only [Logarithm.PeriodRings.completionMapComponent, RingHom.comp_apply, AlgHom.toRingHom_eq_coe,
    AlgHom.coe_toRingHom, Logarithm.PeriodRings.crystallineLog_mod, Ideal.quotientMap_mk, map_sum,
    uncompletedMap_logTerm]

def galoisACrisMap (σ : PeriodInvariants.PeriodRing.PadicGalois p) : Logarithm.PeriodRings.ACris p →+* Logarithm.PeriodRings.ACris p :=
  completedMap p (PeriodInvariants.PeriodRing.galoisIntegerEquiv p σ)

/-- The actual completed Galois map sends t to χ(σ)t. -/
theorem galoisACrisMap_period (σ : PeriodInvariants.PeriodRing.PadicGalois p) :
    galoisACrisMap p σ (Logarithm.PeriodRings.cyclotomicPeriod p) =
      Cyclotomic.padicIntToACris p (cyclotomicCharacter ℂ_[p] p (PeriodInvariants.PeriodRing.galoisComplexEquiv p σ)).val *
        Logarithm.PeriodRings.cyclotomicPeriod p := by
  change completedMap p (PeriodInvariants.PeriodRing.galoisIntegerEquiv p σ)
    (Logarithm.PeriodRings.crystallineLog p (Logarithm.PeriodRings.cyclotomicDifference p) (Logarithm.PeriodRings.cyclotomicDifference_thetaModP p)) = _
  rw [completedMap_log]
  have he : PeriodInvariants.PeriodRing.ainfEquiv p (PeriodInvariants.PeriodRing.galoisIntegerEquiv p σ)
      (Logarithm.PeriodRings.cyclotomicDifference p) = Cyclotomic.towerDifference p (Cyclotomic.galoisCyclotomicTower p σ) :=
    Cyclotomic.aInfMap_towerDifference p (PeriodInvariants.PeriodRing.galoisIntegerEquiv p σ).toRingHom (Logarithm.PeriodRings.cyclotomicTower p)
  simpa only [he] using Cyclotomic.galoisCyclotomicLog_character p σ

def positiveMap (f : 𝓞_ℂ_[p] ≃+* 𝓞_ℂ_[p]) : Logarithm.PeriodRings.BCrisPlus p →+* Logarithm.PeriodRings.BCrisPlus p :=
  Localization.awayLift
    ((algebraMap (Logarithm.PeriodRings.ACris p) (Logarithm.PeriodRings.BCrisPlus p)).comp (completedMap p f)) (p : Logarithm.PeriodRings.ACris p)
    (by simpa using IsLocalization.Away.algebraMap_isUnit (p : Logarithm.PeriodRings.ACris p))

theorem positiveMap_algebraMap (f : 𝓞_ℂ_[p] ≃+* 𝓞_ℂ_[p]) (x : Logarithm.PeriodRings.ACris p) :
    positiveMap p f (algebraMap (Logarithm.PeriodRings.ACris p) (Logarithm.PeriodRings.BCrisPlus p) x) =
      algebraMap (Logarithm.PeriodRings.ACris p) (Logarithm.PeriodRings.BCrisPlus p) (completedMap p f x) := by
  unfold positiveMap
  rw [IsLocalization.Away.lift_eq]
  rfl

theorem galoisPositiveMap_period (σ : PeriodInvariants.PeriodRing.PadicGalois p) :
    positiveMap p (PeriodInvariants.PeriodRing.galoisIntegerEquiv p σ)
      (algebraMap (Logarithm.PeriodRings.ACris p) (Logarithm.PeriodRings.BCrisPlus p) (Logarithm.PeriodRings.cyclotomicPeriod p)) =
      algebraMap (Logarithm.PeriodRings.ACris p) (Logarithm.PeriodRings.BCrisPlus p)
        (Cyclotomic.padicIntToACris p (cyclotomicCharacter ℂ_[p] p (PeriodInvariants.PeriodRing.galoisComplexEquiv p σ)).val) *
      algebraMap (Logarithm.PeriodRings.ACris p) (Logarithm.PeriodRings.BCrisPlus p) (Logarithm.PeriodRings.cyclotomicPeriod p) := by
  rw [positiveMap_algebraMap]
  change algebraMap (Logarithm.PeriodRings.ACris p) (Logarithm.PeriodRings.BCrisPlus p) (galoisACrisMap p σ (Logarithm.PeriodRings.cyclotomicPeriod p)) = _
  rw [galoisACrisMap_period, map_mul]

theorem galois_period_isUnit (σ : PeriodInvariants.PeriodRing.PadicGalois p) :
    IsUnit (((algebraMap (Logarithm.PeriodRings.BCrisPlus p) (Logarithm.PeriodRings.BCris p)).comp
      (positiveMap p (PeriodInvariants.PeriodRing.galoisIntegerEquiv p σ)))
        (algebraMap (Logarithm.PeriodRings.ACris p) (Logarithm.PeriodRings.BCrisPlus p) (Logarithm.PeriodRings.cyclotomicPeriod p))) := by
  rw [RingHom.comp_apply, galoisPositiveMap_period, map_mul]
  exact ((((cyclotomicCharacter ℂ_[p] p (PeriodInvariants.PeriodRing.galoisComplexEquiv p σ)).isUnit.map
      (Cyclotomic.padicIntToACris p)).map (algebraMap (Logarithm.PeriodRings.ACris p) (Logarithm.PeriodRings.BCrisPlus p))).map
        (algebraMap (Logarithm.PeriodRings.BCrisPlus p) (Logarithm.PeriodRings.BCris p))).mul
    (IsLocalization.Away.algebraMap_isUnit
      (algebraMap (Logarithm.PeriodRings.ACris p) (Logarithm.PeriodRings.BCrisPlus p) (Logarithm.PeriodRings.cyclotomicPeriod p)))

/-- The Galois map extends to B_cris because χ(σ)t is invertible there. -/
def galoisBCrisMap (σ : PeriodInvariants.PeriodRing.PadicGalois p) : Logarithm.PeriodRings.BCris p →+* Logarithm.PeriodRings.BCris p :=
  Localization.awayLift
    ((algebraMap (Logarithm.PeriodRings.BCrisPlus p) (Logarithm.PeriodRings.BCris p)).comp
      (positiveMap p (PeriodInvariants.PeriodRing.galoisIntegerEquiv p σ)))
    (algebraMap (Logarithm.PeriodRings.ACris p) (Logarithm.PeriodRings.BCrisPlus p) (Logarithm.PeriodRings.cyclotomicPeriod p)) (galois_period_isUnit p σ)

theorem galoisBCrisMap_algebraMap (σ : PeriodInvariants.PeriodRing.PadicGalois p) (x : Logarithm.PeriodRings.BCrisPlus p) :
    galoisBCrisMap p σ (algebraMap (Logarithm.PeriodRings.BCrisPlus p) (Logarithm.PeriodRings.BCris p) x) =
      algebraMap (Logarithm.PeriodRings.BCrisPlus p) (Logarithm.PeriodRings.BCris p)
        (positiveMap p (PeriodInvariants.PeriodRing.galoisIntegerEquiv p σ) x) :=
  IsLocalization.Away.lift_eq _ (galois_period_isUnit p σ) x

theorem fractionMap_one : (PeriodInvariants.PeriodRing.ainfFractionEquiv p 1).toRingHom =
    RingHom.id (Logarithm.PeriodRings.AInfFractionField p) := by
  apply IsFractionRing.ringHom_ext (A := Logarithm.PeriodRings.AInf p)
  intro x
  change PeriodInvariants.PeriodRing.ainfFractionEquiv p 1
    (algebraMap (Logarithm.PeriodRings.AInf p) (Logarithm.PeriodRings.AInfFractionField p) x) = algebraMap (Logarithm.PeriodRings.AInf p) (Logarithm.PeriodRings.AInfFractionField p) x
  rw [PeriodInvariants.PeriodRing.ainfFractionEquiv_algebraMap]
  change algebraMap (Logarithm.PeriodRings.AInf p) (Logarithm.PeriodRings.AInfFractionField p)
    (PeriodInvariants.PeriodRing.ainfMap p (RingHom.id 𝓞_ℂ_[p]) x) = _
  rw [PeriodInvariants.PeriodRing.ainfMap_id, RingHom.id_apply]

theorem fractionMap_mul (f g : 𝓞_ℂ_[p] ≃+* 𝓞_ℂ_[p]) :
    (PeriodInvariants.PeriodRing.ainfFractionEquiv p (f * g)).toRingHom =
      (PeriodInvariants.PeriodRing.ainfFractionEquiv p f).toRingHom.comp
        (PeriodInvariants.PeriodRing.ainfFractionEquiv p g).toRingHom := by
  apply IsFractionRing.ringHom_ext (A := Logarithm.PeriodRings.AInf p)
  intro x
  change PeriodInvariants.PeriodRing.ainfFractionEquiv p (f * g)
      (algebraMap (Logarithm.PeriodRings.AInf p) (Logarithm.PeriodRings.AInfFractionField p) x) =
    PeriodInvariants.PeriodRing.ainfFractionEquiv p f
      (PeriodInvariants.PeriodRing.ainfFractionEquiv p g (algebraMap (Logarithm.PeriodRings.AInf p) (Logarithm.PeriodRings.AInfFractionField p) x))
  rw [PeriodInvariants.PeriodRing.ainfFractionEquiv_algebraMap,
    PeriodInvariants.PeriodRing.ainfFractionEquiv_algebraMap, PeriodInvariants.PeriodRing.ainfFractionEquiv_algebraMap]
  change algebraMap (Logarithm.PeriodRings.AInf p) (Logarithm.PeriodRings.AInfFractionField p)
      (PeriodInvariants.PeriodRing.ainfMap p (f.toRingHom.comp g.toRingHom) x) =
    algebraMap (Logarithm.PeriodRings.AInf p) (Logarithm.PeriodRings.AInfFractionField p)
      (PeriodInvariants.PeriodRing.ainfMap p f.toRingHom (PeriodInvariants.PeriodRing.ainfMap p g.toRingHom x))
  rw [PeriodInvariants.PeriodRing.ainfMap_comp, RingHom.comp_apply]

theorem uncompletedMap_one : uncompletedMap p 1 = RingHom.id _ := by
  apply RingHom.ext
  intro x
  apply Subtype.ext
  change PeriodInvariants.PeriodRing.ainfFractionEquiv p 1 (x : Logarithm.PeriodRings.AInfFractionField p) =
    (x : Logarithm.PeriodRings.AInfFractionField p)
  exact DFunLike.congr_fun (fractionMap_one p) (x : Logarithm.PeriodRings.AInfFractionField p)

theorem uncompletedMap_mul (f g : 𝓞_ℂ_[p] ≃+* 𝓞_ℂ_[p]) :
    uncompletedMap p (f * g) = (uncompletedMap p f).comp (uncompletedMap p g) := by
  apply RingHom.ext
  intro x
  apply Subtype.ext
  change PeriodInvariants.PeriodRing.ainfFractionEquiv p (f * g) (x : Logarithm.PeriodRings.AInfFractionField p) =
    PeriodInvariants.PeriodRing.ainfFractionEquiv p f (PeriodInvariants.PeriodRing.ainfFractionEquiv p g (x : Logarithm.PeriodRings.AInfFractionField p))
  exact DFunLike.congr_fun (fractionMap_mul p f g) (x : Logarithm.PeriodRings.AInfFractionField p)

theorem completedMap_one : completedMap p 1 = RingHom.id _ := by
  unfold completedMap
  simp only [uncompletedMap_one]
  exact DeRham.completionMap_id _

theorem completedMap_mul (f g : 𝓞_ℂ_[p] ≃+* 𝓞_ℂ_[p]) :
    completedMap p (f * g) = (completedMap p f).comp (completedMap p g) := by
  unfold completedMap
  rw [DeRham.completionMap_comp _ _ _ _ _
    (show (Ideal.span {(p : Logarithm.PeriodRings.ACrisUncompleted p)}).map
        ((uncompletedMap p f).comp (uncompletedMap p g)) ≤
      Ideal.span {(p : Logarithm.PeriodRings.ACrisUncompleted p)} by
        rw [← uncompletedMap_mul]
        exact uncompletedMap_preserves_p p (f * g))]
  congr 1
  exact uncompletedMap_mul p f g

theorem positiveMap_one : positiveMap p 1 = RingHom.id _ := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (p : Logarithm.PeriodRings.ACris p))
  ext x
  simp only [RingHom.comp_apply, positiveMap_algebraMap, completedMap_one, RingHom.id_apply]

theorem positiveMap_mul (f g : 𝓞_ℂ_[p] ≃+* 𝓞_ℂ_[p]) :
    positiveMap p (f * g) = (positiveMap p f).comp (positiveMap p g) := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (p : Logarithm.PeriodRings.ACris p))
  ext x
  simp only [RingHom.comp_apply, positiveMap_algebraMap, completedMap_mul]

theorem galoisBCrisMap_one : galoisBCrisMap p 1 = RingHom.id _ := by
  have hcoeff : PeriodInvariants.PeriodRing.galoisIntegerEquiv p 1 = 1 :=
    (DeRham.galoisIntegerAction p).map_one
  apply IsLocalization.ringHom_ext
    (Submonoid.powers (algebraMap (Logarithm.PeriodRings.ACris p) (Logarithm.PeriodRings.BCrisPlus p) (Logarithm.PeriodRings.cyclotomicPeriod p)))
  ext x
  simp only [RingHom.comp_apply, galoisBCrisMap_algebraMap, hcoeff,
    positiveMap_one, RingHom.id_apply]

theorem galoisBCrisMap_mul (σ τ : PeriodInvariants.PeriodRing.PadicGalois p) :
    galoisBCrisMap p (σ * τ) = (galoisBCrisMap p σ).comp (galoisBCrisMap p τ) := by
  have hcoeff : PeriodInvariants.PeriodRing.galoisIntegerEquiv p (σ * τ) =
      PeriodInvariants.PeriodRing.galoisIntegerEquiv p σ * PeriodInvariants.PeriodRing.galoisIntegerEquiv p τ :=
    (DeRham.galoisIntegerAction p).map_mul σ τ
  apply IsLocalization.ringHom_ext
    (Submonoid.powers (algebraMap (Logarithm.PeriodRings.ACris p) (Logarithm.PeriodRings.BCrisPlus p) (Logarithm.PeriodRings.cyclotomicPeriod p)))
  ext x
  simp only [RingHom.comp_apply, galoisBCrisMap_algebraMap, hcoeff, positiveMap_mul]

def galoisBCrisEquiv (σ : PeriodInvariants.PeriodRing.PadicGalois p) : Logarithm.PeriodRings.BCris p ≃+* Logarithm.PeriodRings.BCris p :=
  RingEquiv.ofRingHom (galoisBCrisMap p σ) (galoisBCrisMap p σ⁻¹)
    (by rw [← galoisBCrisMap_mul, mul_inv_cancel, galoisBCrisMap_one])
    (by rw [← galoisBCrisMap_mul, inv_mul_cancel, galoisBCrisMap_one])

/-- The actual absolute Galois action on B_cris, with the group laws proved. -/
def galoisBCrisAction : PeriodInvariants.PeriodRing.PadicGalois p →* (Logarithm.PeriodRings.BCris p ≃+* Logarithm.PeriodRings.BCris p) where
  toFun := galoisBCrisEquiv p
  map_one' := by
    apply RingEquiv.toRingHom_injective
    exact galoisBCrisMap_one p
  map_mul' σ τ := by
    apply RingEquiv.toRingHom_injective
    exact galoisBCrisMap_mul p σ τ

end NumberTheory.PadicHodge.WeakAdmissibility.Galois

namespace NumberTheory.PadicHodge.WeakAdmissibility.Galois.PeriodStructure

/-!
Compatibility of Frobenius and the actual Galois action on B_cris.
-/

open OAI.NumberTheory.PadicHodge.WeakAdmissibility.Logarithm.PeriodRings OAI.NumberTheory.PadicHodge.WeakAdmissibility.Logarithm OAI.NumberTheory.PadicHodge.WeakAdmissibility.Galois OAI.NumberTheory.PadicHodge.WeakAdmissibility.Cyclotomic

variable (p : ℕ) [Fact p.Prime]

theorem aInfMap_frobenius (f : 𝓞_ℂ_[p] ≃+* 𝓞_ℂ_[p]) (x : Logarithm.PeriodRings.AInf p) :
    PeriodInvariants.PeriodRing.ainfEquiv p f (Logarithm.PeriodRings.aInfFrobenius p x) =
      Logarithm.PeriodRings.aInfFrobenius p (PeriodInvariants.PeriodRing.ainfEquiv p f x) := by
  change WittVector.map (PeriodInvariants.PeriodRing.tiltMap p f.toRingHom) (WittVector.frobenius x) =
    WittVector.frobenius (WittVector.map (PeriodInvariants.PeriodRing.tiltMap p f.toRingHom) x)
  ext n
  simp only [WittVector.map_coeff, WittVector.coeff_frobenius_charP, map_pow]

theorem fractionMap_frobenius (f : 𝓞_ℂ_[p] ≃+* 𝓞_ℂ_[p]) :
    (PeriodInvariants.PeriodRing.ainfFractionEquiv p f).toRingHom.comp (Logarithm.PeriodRings.fractionFrobenius p).toRingHom =
      (Logarithm.PeriodRings.fractionFrobenius p).toRingHom.comp (PeriodInvariants.PeriodRing.ainfFractionEquiv p f).toRingHom := by
  apply IsFractionRing.ringHom_ext (A := Logarithm.PeriodRings.AInf p)
  intro x
  change PeriodInvariants.PeriodRing.ainfFractionEquiv p f
      (Logarithm.PeriodRings.fractionFrobenius p (algebraMap (Logarithm.PeriodRings.AInf p) (Logarithm.PeriodRings.AInfFractionField p) x)) =
    Logarithm.PeriodRings.fractionFrobenius p
      (PeriodInvariants.PeriodRing.ainfFractionEquiv p f (algebraMap (Logarithm.PeriodRings.AInf p) (Logarithm.PeriodRings.AInfFractionField p) x))
  rw [Logarithm.PeriodRings.fractionFrobenius_algebraMap, PeriodInvariants.PeriodRing.ainfFractionEquiv_algebraMap,
    PeriodInvariants.PeriodRing.ainfFractionEquiv_algebraMap, Logarithm.PeriodRings.fractionFrobenius_algebraMap]
  exact congrArg (algebraMap (Logarithm.PeriodRings.AInf p) (Logarithm.PeriodRings.AInfFractionField p)) (aInfMap_frobenius p f x)

theorem uncompletedMap_frobenius (f : 𝓞_ℂ_[p] ≃+* 𝓞_ℂ_[p]) :
    (uncompletedMap p f).comp (Logarithm.PeriodRings.aCrisUncompletedFrobenius p) =
      (Logarithm.PeriodRings.aCrisUncompletedFrobenius p).comp (uncompletedMap p f) := by
  apply RingHom.ext
  intro x
  apply Subtype.ext
  change PeriodInvariants.PeriodRing.ainfFractionEquiv p f (Logarithm.PeriodRings.fractionFrobenius p (x : Logarithm.PeriodRings.AInfFractionField p)) =
    Logarithm.PeriodRings.fractionFrobenius p (PeriodInvariants.PeriodRing.ainfFractionEquiv p f (x : Logarithm.PeriodRings.AInfFractionField p))
  exact DFunLike.congr_fun (fractionMap_frobenius p f) (x : Logarithm.PeriodRings.AInfFractionField p)

theorem completedMap_frobenius (f : 𝓞_ℂ_[p] ≃+* 𝓞_ℂ_[p]) :
    (completedMap p f).comp (Logarithm.PeriodRings.aCrisFrobenius p) =
      (Logarithm.PeriodRings.aCrisFrobenius p).comp (completedMap p f) := by
  unfold completedMap Logarithm.PeriodRings.aCrisFrobenius
  rw [DeRham.completionMap_comp _ _ _ _ _
    (show (Ideal.span {(p : Logarithm.PeriodRings.ACrisUncompleted p)}).map
        ((uncompletedMap p f).comp (Logarithm.PeriodRings.aCrisUncompletedFrobenius p)) ≤
      Ideal.span {(p : Logarithm.PeriodRings.ACrisUncompleted p)} by rw [Ideal.map_span]; simp)]
  rw [DeRham.completionMap_comp _ _ _ _ _
    (show (Ideal.span {(p : Logarithm.PeriodRings.ACrisUncompleted p)}).map
        ((Logarithm.PeriodRings.aCrisUncompletedFrobenius p).comp (uncompletedMap p f)) ≤
      Ideal.span {(p : Logarithm.PeriodRings.ACrisUncompleted p)} by rw [Ideal.map_span]; simp)]
  congr 1
  exact uncompletedMap_frobenius p f

theorem positiveMap_frobenius (f : 𝓞_ℂ_[p] ≃+* 𝓞_ℂ_[p]) :
    (positiveMap p f).comp (Logarithm.PeriodRings.bCrisPlusFrobenius p) =
      (Logarithm.PeriodRings.bCrisPlusFrobenius p).comp (positiveMap p f) := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (p : Logarithm.PeriodRings.ACris p))
  ext x
  simp only [RingHom.comp_apply, positiveMap_algebraMap, Logarithm.PeriodRings.bCrisPlusFrobenius_algebraMap]
  exact congrArg (algebraMap (Logarithm.PeriodRings.ACris p) (Logarithm.PeriodRings.BCrisPlus p))
    (DFunLike.congr_fun (completedMap_frobenius p f) x)

/-- Frobenius preserves the Galois invariants because the two actual maps commute. -/
theorem galoisBCrisMap_frobenius (σ : PeriodInvariants.PeriodRing.PadicGalois p) :
    (galoisBCrisMap p σ).comp (Logarithm.bCrisFrobenius p) =
      (Logarithm.bCrisFrobenius p).comp (galoisBCrisMap p σ) := by
  apply IsLocalization.ringHom_ext
    (Submonoid.powers (algebraMap (Logarithm.PeriodRings.ACris p) (Logarithm.PeriodRings.BCrisPlus p) (Logarithm.PeriodRings.cyclotomicPeriod p)))
  ext x
  simp only [RingHom.comp_apply, galoisBCrisMap_algebraMap, Logarithm.bCrisFrobenius_algebraMap]
  exact congrArg (algebraMap (Logarithm.PeriodRings.BCrisPlus p) (Logarithm.PeriodRings.BCris p))
    (DFunLike.congr_fun (positiveMap_frobenius p (PeriodInvariants.PeriodRing.galoisIntegerEquiv p σ)) x)

def padicIntToPositive : ℤ_[p] →+* Logarithm.PeriodRings.BCrisPlus p :=
  (algebraMap (Logarithm.PeriodRings.ACris p) (Logarithm.PeriodRings.BCrisPlus p)).comp (Cyclotomic.padicIntToACris p)

/-- The canonical rational p-adic coefficient map, obtained by localization. -/
def padicToPositive : ℚ_[p] →+* Logarithm.PeriodRings.BCrisPlus p :=
  IsLocalization.lift (S := ℚ_[p]) (g := padicIntToPositive p)
    (fun y : nonZeroDivisors ℤ_[p] => PeriodInvariants.PeriodRing.padicInt_map_nonzero_isUnit p
      (padicIntToPositive p)
      (by simpa only [map_natCast] using IsLocalization.Away.algebraMap_isUnit (p : Logarithm.PeriodRings.ACris p))
      (mem_nonZeroDivisors_iff_ne_zero.mp y.property))

theorem padicToPositive_int (x : ℤ_[p]) :
    padicToPositive p (algebraMap ℤ_[p] ℚ_[p] x) = padicIntToPositive p x := by
  unfold padicToPositive
  rw [IsLocalization.lift_eq]

def padicToBCris : ℚ_[p] →+* Logarithm.PeriodRings.BCris p :=
  (algebraMap (Logarithm.PeriodRings.BCrisPlus p) (Logarithm.PeriodRings.BCris p)).comp (padicToPositive p)

instance positive_padicAlgebra : Algebra ℚ_[p] (Logarithm.PeriodRings.BCrisPlus p) := (padicToPositive p).toAlgebra

instance bCris_padicAlgebra : Algebra ℚ_[p] (Logarithm.PeriodRings.BCris p) := (padicToBCris p).toAlgebra

instance bCris_padicModule : Module ℚ_[p] (Logarithm.PeriodRings.BCris p) := Algebra.toModule

theorem uncompletedMap_algebraMap (f : 𝓞_ℂ_[p] ≃+* 𝓞_ℂ_[p]) (x : Logarithm.PeriodRings.AInf p) :
    uncompletedMap p f (algebraMap (Logarithm.PeriodRings.AInf p) (Logarithm.PeriodRings.ACrisUncompleted p) x) =
      algebraMap (Logarithm.PeriodRings.AInf p) (Logarithm.PeriodRings.ACrisUncompleted p) (PeriodInvariants.PeriodRing.ainfEquiv p f x) := by
  apply Subtype.ext
  change PeriodInvariants.PeriodRing.ainfFractionEquiv p f
    (algebraMap (Logarithm.PeriodRings.AInf p) (Logarithm.PeriodRings.AInfFractionField p) x) = _
  exact PeriodInvariants.PeriodRing.ainfFractionEquiv_algebraMap p f x

theorem completedMap_algebraMap (f : 𝓞_ℂ_[p] ≃+* 𝓞_ℂ_[p]) (x : Logarithm.PeriodRings.ACrisUncompleted p) :
    completedMap p f (algebraMap (Logarithm.PeriodRings.ACrisUncompleted p) (Logarithm.PeriodRings.ACris p) x) =
      algebraMap (Logarithm.PeriodRings.ACrisUncompleted p) (Logarithm.PeriodRings.ACris p) (uncompletedMap p f x) :=
  Logarithm.PeriodRings.completionMap_of _ _ (uncompletedMap_preserves_p p f) x

theorem completedMap_padicInt (f : 𝓞_ℂ_[p] ≃+* 𝓞_ℂ_[p]) (x : ℤ_[p]) :
    completedMap p f (Cyclotomic.padicIntToACris p x) = Cyclotomic.padicIntToACris p x := by
  rw [Cyclotomic.padicIntToACris, RingHom.comp_apply, completedMap_algebraMap]
  change algebraMap (Logarithm.PeriodRings.ACrisUncompleted p) (Logarithm.PeriodRings.ACris p)
    (uncompletedMap p f (algebraMap (Logarithm.PeriodRings.AInf p) (Logarithm.PeriodRings.ACrisUncompleted p) (Logarithm.PeriodRings.padicIntToAInf p x))) = _
  rw [uncompletedMap_algebraMap]
  have he : PeriodInvariants.PeriodRing.ainfEquiv p f (Logarithm.PeriodRings.padicIntToAInf p x) = Logarithm.PeriodRings.padicIntToAInf p x :=
    PeriodInvariants.PeriodRing.ainfMap_padicInt p f.toRingHom x
  rw [he]
  rfl

theorem positiveMap_padicInt (f : 𝓞_ℂ_[p] ≃+* 𝓞_ℂ_[p]) (x : ℤ_[p]) :
    positiveMap p f (padicIntToPositive p x) = padicIntToPositive p x := by
  rw [padicIntToPositive, RingHom.comp_apply, positiveMap_algebraMap, completedMap_padicInt]

theorem positiveMap_padic (f : 𝓞_ℂ_[p] ≃+* 𝓞_ℂ_[p]) (x : ℚ_[p]) :
    positiveMap p f (padicToPositive p x) = padicToPositive p x := by
  have he : (positiveMap p f).comp (padicToPositive p) = padicToPositive p := by
    apply IsLocalization.ringHom_ext (nonZeroDivisors ℤ_[p])
    ext a
    change positiveMap p f (padicToPositive p (algebraMap ℤ_[p] ℚ_[p] a)) =
      padicToPositive p (algebraMap ℤ_[p] ℚ_[p] a)
    rw [padicToPositive_int, positiveMap_padicInt]
  exact DFunLike.congr_fun he x

theorem galoisBCrisMap_padic (σ : PeriodInvariants.PeriodRing.PadicGalois p) (x : ℚ_[p]) :
    galoisBCrisMap p σ (padicToBCris p x) = padicToBCris p x := by
  rw [padicToBCris, RingHom.comp_apply, galoisBCrisMap_algebraMap, positiveMap_padic]

/-- The actual Galois automorphisms are linear over the canonical ℚ_p coefficients. -/
def galoisBCrisAlgEquiv (σ : PeriodInvariants.PeriodRing.PadicGalois p) : Logarithm.PeriodRings.BCris p ≃ₐ[ℚ_[p]] Logarithm.PeriodRings.BCris p :=
  { galoisBCrisEquiv p σ with commutes' := galoisBCrisMap_padic p σ }

theorem aInfFrobenius_padicInt (x : ℤ_[p]) :
    Logarithm.PeriodRings.aInfFrobenius p (Logarithm.PeriodRings.padicIntToAInf p x) = Logarithm.PeriodRings.padicIntToAInf p x := by
  change WittVector.frobenius
      (WittVector.map (ZMod.castHom (dvd_refl p) (PreTilt 𝓞_ℂ_[p] p)) ((WittVector.equiv p).symm x)) =
    WittVector.map (ZMod.castHom (dvd_refl p) (PreTilt 𝓞_ℂ_[p] p)) ((WittVector.equiv p).symm x)
  ext n
  simp only [WittVector.coeff_frobenius_charP, WittVector.map_coeff]
  rw [← map_pow, ZMod.pow_card]

theorem uncompletedFrobenius_algebraMap (x : Logarithm.PeriodRings.AInf p) :
    Logarithm.PeriodRings.aCrisUncompletedFrobenius p (algebraMap (Logarithm.PeriodRings.AInf p) (Logarithm.PeriodRings.ACrisUncompleted p) x) =
      algebraMap (Logarithm.PeriodRings.AInf p) (Logarithm.PeriodRings.ACrisUncompleted p) (Logarithm.PeriodRings.aInfFrobenius p x) := by
  apply Subtype.ext
  change Logarithm.PeriodRings.fractionFrobenius p (algebraMap (Logarithm.PeriodRings.AInf p) (Logarithm.PeriodRings.AInfFractionField p) x) = _
  exact Logarithm.PeriodRings.fractionFrobenius_algebraMap p x

theorem aCrisFrobenius_algebraMap (x : Logarithm.PeriodRings.ACrisUncompleted p) :
    Logarithm.PeriodRings.aCrisFrobenius p (algebraMap (Logarithm.PeriodRings.ACrisUncompleted p) (Logarithm.PeriodRings.ACris p) x) =
      algebraMap (Logarithm.PeriodRings.ACrisUncompleted p) (Logarithm.PeriodRings.ACris p) (Logarithm.PeriodRings.aCrisUncompletedFrobenius p x) :=
  Logarithm.PeriodRings.completionMap_of _ _ (Logarithm.PeriodRings.aCrisUncompletedFrobenius_preserves_p p) x

theorem aCrisFrobenius_padicInt (x : ℤ_[p]) :
    Logarithm.PeriodRings.aCrisFrobenius p (Cyclotomic.padicIntToACris p x) = Cyclotomic.padicIntToACris p x := by
  rw [Cyclotomic.padicIntToACris, RingHom.comp_apply, aCrisFrobenius_algebraMap]
  change algebraMap (Logarithm.PeriodRings.ACrisUncompleted p) (Logarithm.PeriodRings.ACris p)
    (Logarithm.PeriodRings.aCrisUncompletedFrobenius p
      (algebraMap (Logarithm.PeriodRings.AInf p) (Logarithm.PeriodRings.ACrisUncompleted p) (Logarithm.PeriodRings.padicIntToAInf p x))) = _
  rw [uncompletedFrobenius_algebraMap, aInfFrobenius_padicInt]
  rfl

theorem bCrisPlusFrobenius_padicInt (x : ℤ_[p]) :
    Logarithm.PeriodRings.bCrisPlusFrobenius p (padicIntToPositive p x) = padicIntToPositive p x := by
  rw [padicIntToPositive, RingHom.comp_apply, Logarithm.PeriodRings.bCrisPlusFrobenius_algebraMap, aCrisFrobenius_padicInt]

theorem bCrisPlusFrobenius_padic (x : ℚ_[p]) :
    Logarithm.PeriodRings.bCrisPlusFrobenius p (padicToPositive p x) = padicToPositive p x := by
  have he : (Logarithm.PeriodRings.bCrisPlusFrobenius p).comp (padicToPositive p) = padicToPositive p := by
    apply IsLocalization.ringHom_ext (nonZeroDivisors ℤ_[p])
    ext a
    change Logarithm.PeriodRings.bCrisPlusFrobenius p (padicToPositive p (algebraMap ℤ_[p] ℚ_[p] a)) =
      padicToPositive p (algebraMap ℤ_[p] ℚ_[p] a)
    rw [padicToPositive_int, bCrisPlusFrobenius_padicInt]
  exact DFunLike.congr_fun he x

theorem bCrisFrobenius_padic (x : ℚ_[p]) :
    Logarithm.bCrisFrobenius p (padicToBCris p x) = padicToBCris p x := by
  rw [padicToBCris, RingHom.comp_apply, Logarithm.bCrisFrobenius_algebraMap, bCrisPlusFrobenius_padic]

/-- Crystalline Frobenius is linear over the canonical ℚ_p coefficient field. -/
def bCrisFrobeniusAlg : Logarithm.PeriodRings.BCris p →ₐ[ℚ_[p]] Logarithm.PeriodRings.BCris p :=
  { Logarithm.bCrisFrobenius p with commutes' := bCrisFrobenius_padic p }

def periodRepresentation : Representation ℚ_[p] (PeriodInvariants.PeriodRing.PadicGalois p) (Logarithm.PeriodRings.BCris p) where
  toFun σ := (galoisBCrisAlgEquiv p σ).toLinearMap
  map_one' := by
    apply LinearMap.ext
    intro x
    exact DFunLike.congr_fun (galoisBCrisMap_one p) x
  map_mul' σ τ := by
    apply LinearMap.ext
    intro x
    exact DFunLike.congr_fun (galoisBCrisMap_mul p σ τ) x

theorem periodRepresentation_frobenius (σ : PeriodInvariants.PeriodRing.PadicGalois p) (x : Logarithm.PeriodRings.BCris p) :
    periodRepresentation p σ (bCrisFrobeniusAlg p x) =
      bCrisFrobeniusAlg p (periodRepresentation p σ x) :=
  DFunLike.congr_fun (galoisBCrisMap_frobenius p σ) x

end NumberTheory.PadicHodge.WeakAdmissibility.Galois.PeriodStructure

end

end OAI
