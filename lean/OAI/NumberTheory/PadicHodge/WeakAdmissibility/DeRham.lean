import OAI.NumberTheory.PadicHodge.WeakAdmissibility.Logarithm
import OAI.NumberTheory.PadicHodge.PeriodInvariants.PeriodRing

/-! # De Rham -/

namespace OAI.NumberTheory.PadicHodge.WeakAdmissibility.DeRham

noncomputable section

/-!
Concrete theta maps and the actual absolute Galois action on B_dR^+ for WeakAdmissibility.
The action preserves the nonnegative theta-adic filtration. The crystalline
comparison map and integer-indexed filtration require further constructions.
-/

open OAI.NumberTheory.PadicHodge.WeakAdmissibility.Logarithm.PeriodRings

variable (p : ℕ) [Fact p.Prime]

abbrev IntegerLocalization := Localization.Away (p : 𝓞_ℂ_[p])

def bInfTheta : Logarithm.PeriodRings.BInf p →+* IntegerLocalization p := fontaineThetaInvertP 𝓞_ℂ_[p] p

theorem bInfTheta_algebraMap (x : Logarithm.PeriodRings.AInf p) :
    bInfTheta p (algebraMap (Logarithm.PeriodRings.AInf p) (Logarithm.PeriodRings.BInf p) x) =
      algebraMap 𝓞_ℂ_[p] (IntegerLocalization p) (Logarithm.PeriodRings.theta p x) := by
  unfold bInfTheta fontaineThetaInvertP
  rw [IsLocalization.Away.lift_eq]
  rfl

abbrev deRhamIdeal : Ideal (Logarithm.PeriodRings.BInf p) := RingHom.ker (bInfTheta p)

/-- The defining map to the actual theta-adic de Rham completion. -/
def bInfToBdRPlus : Logarithm.PeriodRings.BInf p →+* Logarithm.PeriodRings.BdRPlus p :=
  algebraMap (Logarithm.PeriodRings.BInf p) (AdicCompletion (deRhamIdeal p) (Logarithm.PeriodRings.BInf p))

def thetaReduction : (Logarithm.PeriodRings.BInf p) ⧸ (deRhamIdeal p) ^ 1 →+* IntegerLocalization p :=
  Ideal.Quotient.lift _ (bInfTheta p) (by
    intro a ha
    exact RingHom.mem_ker.mp (by simpa only [pow_one] using ha))

/-- Theta on B_dR^+, obtained from its first defining quotient. -/
def thetaBdRPlus : Logarithm.PeriodRings.BdRPlus p →+* IntegerLocalization p :=
  (thetaReduction p).comp (AdicCompletion.evalₐ (deRhamIdeal p) 1).toRingHom

theorem thetaBdRPlus_bInf (x : Logarithm.PeriodRings.BInf p) :
    thetaBdRPlus p (bInfToBdRPlus p x) = bInfTheta p x := by
  change thetaReduction p (AdicCompletion.evalₐ (deRhamIdeal p) 1
    (AdicCompletion.of (deRhamIdeal p) (Logarithm.PeriodRings.BInf p) x)) = _
  rw [AdicCompletion.evalₐ_of]
  rfl

theorem thetaBdRPlus_aInf (x : Logarithm.PeriodRings.AInf p) :
    thetaBdRPlus p (bInfToBdRPlus p (algebraMap (Logarithm.PeriodRings.AInf p) (Logarithm.PeriodRings.BInf p) x)) =
      algebraMap 𝓞_ℂ_[p] (IntegerLocalization p) (Logarithm.PeriodRings.theta p x) := by
  rw [thetaBdRPlus_bInf, bInfTheta_algebraMap]

def integerLocalizationToCp : IntegerLocalization p →+* ℂ_[p] :=
  Localization.awayLift (algebraMap 𝓞_ℂ_[p] ℂ_[p]) (p : 𝓞_ℂ_[p])
    (by
      apply isUnit_iff_ne_zero.mpr
      simpa only [map_natCast] using
        (show (p : ℂ_[p]) ≠ 0 by exact_mod_cast (Fact.out : p.Prime).ne_zero))

theorem integerLocalizationToCp_algebraMap (x : 𝓞_ℂ_[p]) :
    integerLocalizationToCp p (algebraMap 𝓞_ℂ_[p] (IntegerLocalization p) x) =
      algebraMap 𝓞_ℂ_[p] ℂ_[p] x := by
  unfold integerLocalizationToCp
  rw [IsLocalization.Away.lift_eq]

def thetaBdRPlusCp : Logarithm.PeriodRings.BdRPlus p →+* ℂ_[p] :=
  (integerLocalizationToCp p).comp (thetaBdRPlus p)

instance bdRPlus_charZero : CharZero (Logarithm.PeriodRings.BdRPlus p) where
  cast_injective a b h := by
    have he := congrArg (thetaBdRPlusCp p) h
    simpa only [map_natCast, Nat.cast_inj] using he

/-- The nonnegative theta-adic filtration on B_dR^+. -/
def positiveFiltration (n : ℕ) : Ideal (Logarithm.PeriodRings.BdRPlus p) := (RingHom.ker (thetaBdRPlus p)) ^ n

theorem positiveFiltration_antitone : Antitone (positiveFiltration p) := by
  intro m n hmn
  exact Ideal.pow_le_pow_right hmn

def integerLocalizationMap (f : 𝓞_ℂ_[p] →+* 𝓞_ℂ_[p]) :
    IntegerLocalization p →+* IntegerLocalization p :=
  Localization.awayLift ((algebraMap 𝓞_ℂ_[p] (IntegerLocalization p)).comp f)
    (p : 𝓞_ℂ_[p]) (by simpa using IsLocalization.Away.algebraMap_isUnit (p : 𝓞_ℂ_[p]))

theorem integerLocalizationMap_algebraMap (f : 𝓞_ℂ_[p] →+* 𝓞_ℂ_[p]) (x : 𝓞_ℂ_[p]) :
    integerLocalizationMap p f (algebraMap 𝓞_ℂ_[p] (IntegerLocalization p) x) =
      algebraMap 𝓞_ℂ_[p] (IntegerLocalization p) (f x) := by
  unfold integerLocalizationMap
  rw [IsLocalization.Away.lift_eq]
  rfl

def bInfMap (f : 𝓞_ℂ_[p] →+* 𝓞_ℂ_[p]) : Logarithm.PeriodRings.BInf p →+* Logarithm.PeriodRings.BInf p :=
  Localization.awayLift
    ((algebraMap (Logarithm.PeriodRings.AInf p) (Logarithm.PeriodRings.BInf p)).comp (PeriodInvariants.PeriodRing.ainfMap p f))
    (p : Logarithm.PeriodRings.AInf p) (by simpa using IsLocalization.Away.algebraMap_isUnit (p : Logarithm.PeriodRings.AInf p))

theorem bInfMap_algebraMap (f : 𝓞_ℂ_[p] →+* 𝓞_ℂ_[p]) (x : Logarithm.PeriodRings.AInf p) :
    bInfMap p f (algebraMap (Logarithm.PeriodRings.AInf p) (Logarithm.PeriodRings.BInf p) x) =
      algebraMap (Logarithm.PeriodRings.AInf p) (Logarithm.PeriodRings.BInf p) (PeriodInvariants.PeriodRing.ainfMap p f x) := by
  unfold bInfMap
  rw [IsLocalization.Away.lift_eq]
  rfl

theorem bInfTheta_natural (f : 𝓞_ℂ_[p] →+* 𝓞_ℂ_[p]) (x : Logarithm.PeriodRings.BInf p) :
    bInfTheta p (bInfMap p f x) = integerLocalizationMap p f (bInfTheta p x) := by
  have he : (bInfTheta p).comp (bInfMap p f) =
      (integerLocalizationMap p f).comp (bInfTheta p) := by
    apply IsLocalization.ringHom_ext (Submonoid.powers (p : Logarithm.PeriodRings.AInf p))
    ext a
    simp only [RingHom.comp_apply, bInfMap_algebraMap, bInfTheta_algebraMap,
      integerLocalizationMap_algebraMap]
    congr 1
    exact PeriodInvariants.PeriodRing.theta_natural p f a
  exact DFunLike.congr_fun he x

theorem bInfMap_preserves_deRhamIdeal (f : 𝓞_ℂ_[p] →+* 𝓞_ℂ_[p]) :
    (deRhamIdeal p).map (bInfMap p f) ≤ deRhamIdeal p := by
  rw [Ideal.map_le_iff_le_comap]
  intro x hx
  change bInfTheta p (bInfMap p f x) = 0
  rw [bInfTheta_natural, RingHom.mem_ker.mp hx, map_zero]

/-- Endomorphisms of the actual coefficient ring act on the de Rham completion. -/
def bdRPlusMap (f : 𝓞_ℂ_[p] →+* 𝓞_ℂ_[p]) : Logarithm.PeriodRings.BdRPlus p →+* Logarithm.PeriodRings.BdRPlus p :=
  Logarithm.PeriodRings.completionMap (deRhamIdeal p) (bInfMap p f) (bInfMap_preserves_deRhamIdeal p f)

theorem bdRPlusMap_bInf (f : 𝓞_ℂ_[p] →+* 𝓞_ℂ_[p]) (x : Logarithm.PeriodRings.BInf p) :
    bdRPlusMap p f (bInfToBdRPlus p x) = bInfToBdRPlus p (bInfMap p f x) :=
  Logarithm.PeriodRings.completionMap_of (deRhamIdeal p) (bInfMap p f) (bInfMap_preserves_deRhamIdeal p f) x

theorem thetaBdRPlus_natural (f : 𝓞_ℂ_[p] →+* 𝓞_ℂ_[p]) (x : Logarithm.PeriodRings.BdRPlus p) :
    thetaBdRPlus p (bdRPlusMap p f x) = integerLocalizationMap p f (thetaBdRPlus p x) := by
  change AdicCompletion (deRhamIdeal p) (Logarithm.PeriodRings.BInf p) at x
  change thetaReduction p (AdicCompletion.evalₐ (deRhamIdeal p) 1
    (Logarithm.PeriodRings.completionMap (deRhamIdeal p) (bInfMap p f) (bInfMap_preserves_deRhamIdeal p f) x)) = _
  rw [Logarithm.PeriodRings.completionMap, AdicCompletion.evalₐ_liftRingHom]
  change thetaReduction p (Ideal.quotientMap _ (bInfMap p f)
      (Logarithm.PeriodRings.map_preserves_ideal_pow (deRhamIdeal p) (bInfMap p f)
        (bInfMap_preserves_deRhamIdeal p f) 1)
      (AdicCompletion.evalₐ (deRhamIdeal p) 1 x)) =
    integerLocalizationMap p f (thetaReduction p (AdicCompletion.evalₐ (deRhamIdeal p) 1 x))
  generalize AdicCompletion.evalₐ (deRhamIdeal p) 1 x = q
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective q
  exact bInfTheta_natural p f a

theorem bdRPlusMap_preserves_filtration (f : 𝓞_ℂ_[p] →+* 𝓞_ℂ_[p]) (n : ℕ) :
    (positiveFiltration p n).map (bdRPlusMap p f) ≤ positiveFiltration p n := by
  have hker : (RingHom.ker (thetaBdRPlus p)).map (bdRPlusMap p f) ≤
      RingHom.ker (thetaBdRPlus p) := by
    rw [Ideal.map_le_iff_le_comap]
    intro x hx
    change thetaBdRPlus p (bdRPlusMap p f x) = 0
    rw [thetaBdRPlus_natural, RingHom.mem_ker.mp hx, map_zero]
  rw [positiveFiltration, Ideal.map_pow]
  exact pow_le_pow_left' hker n

/-- In particular, each absolute Galois automorphism acts on B_dR^+. -/
def galoisBdRPlusMap (σ : PeriodInvariants.PeriodRing.PadicGalois p) : Logarithm.PeriodRings.BdRPlus p →+* Logarithm.PeriodRings.BdRPlus p :=
  bdRPlusMap p (PeriodInvariants.PeriodRing.galoisIntegerEquiv p σ).toRingHom

theorem galoisBdRPlusMap_preserves_filtration (σ : PeriodInvariants.PeriodRing.PadicGalois p) (n : ℕ) :
    (positiveFiltration p n).map (galoisBdRPlusMap p σ) ≤ positiveFiltration p n :=
  bdRPlusMap_preserves_filtration p _ n

section CompletionFunctor

variable {R : Type*} [CommRing R] (I : Ideal R)

theorem completionMap_id : Logarithm.PeriodRings.completionMap I (RingHom.id R) (by simp) = RingHom.id _ := by
  apply RingHom.ext
  intro x
  apply AdicCompletion.ext_evalₐ
  intro n
  simp only [Logarithm.PeriodRings.completionMap, AdicCompletion.evalₐ_liftRingHom,
    Logarithm.PeriodRings.completionMapComponent, RingHom.comp_apply, AlgHom.toRingHom_eq_coe,
    AlgHom.coe_toRingHom, RingHom.id_apply]
  generalize AdicCompletion.evalₐ I n x = q
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective q
  rfl

theorem completionMap_comp (f g : R →+* R) (hf : I.map f ≤ I) (hg : I.map g ≤ I)
    (hfg : I.map (f.comp g) ≤ I) :
    (Logarithm.PeriodRings.completionMap I f hf).comp (Logarithm.PeriodRings.completionMap I g hg) =
      Logarithm.PeriodRings.completionMap I (f.comp g) hfg := by
  apply RingHom.ext
  intro x
  apply AdicCompletion.ext_evalₐ
  intro n
  simp only [RingHom.comp_apply, Logarithm.PeriodRings.completionMap, AdicCompletion.evalₐ_liftRingHom,
    Logarithm.PeriodRings.completionMapComponent, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom]
  generalize AdicCompletion.evalₐ I n x = q
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective q
  rfl

end CompletionFunctor

theorem bInfMap_id : bInfMap p (RingHom.id 𝓞_ℂ_[p]) = RingHom.id _ := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (p : Logarithm.PeriodRings.AInf p))
  ext x
  simp only [RingHom.comp_apply, bInfMap_algebraMap, PeriodInvariants.PeriodRing.ainfMap_id,
    RingHom.id_apply]

theorem bInfMap_comp (f g : 𝓞_ℂ_[p] →+* 𝓞_ℂ_[p]) :
    bInfMap p (f.comp g) = (bInfMap p f).comp (bInfMap p g) := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (p : Logarithm.PeriodRings.AInf p))
  ext x
  simp only [RingHom.comp_apply, bInfMap_algebraMap, PeriodInvariants.PeriodRing.ainfMap_comp]

theorem bdRPlusMap_id : bdRPlusMap p (RingHom.id 𝓞_ℂ_[p]) = RingHom.id _ := by
  unfold bdRPlusMap
  simp only [bInfMap_id]
  exact completionMap_id (deRhamIdeal p)

theorem bdRPlusMap_comp (f g : 𝓞_ℂ_[p] →+* 𝓞_ℂ_[p]) :
    bdRPlusMap p (f.comp g) = (bdRPlusMap p f).comp (bdRPlusMap p g) := by
  change (Logarithm.PeriodRings.completionMap (deRhamIdeal p) (bInfMap p (f.comp g))
      (bInfMap_preserves_deRhamIdeal p (f.comp g)) :
      AdicCompletion (deRhamIdeal p) (Logarithm.PeriodRings.BInf p) →+* AdicCompletion (deRhamIdeal p) (Logarithm.PeriodRings.BInf p)) =
    (Logarithm.PeriodRings.completionMap (deRhamIdeal p) (bInfMap p f) (bInfMap_preserves_deRhamIdeal p f)).comp
      (Logarithm.PeriodRings.completionMap (deRhamIdeal p) (bInfMap p g) (bInfMap_preserves_deRhamIdeal p g))
  rw [completionMap_comp _ _ _ _ _
    (show (deRhamIdeal p).map ((bInfMap p f).comp (bInfMap p g)) ≤ deRhamIdeal p by
      rw [← bInfMap_comp]
      exact bInfMap_preserves_deRhamIdeal p (f.comp g))]
  congr 1
  exact bInfMap_comp p f g

/-- A coefficient-ring automorphism gives an actual automorphism of B_dR^+. -/
def bdRPlusEquiv (f : 𝓞_ℂ_[p] ≃+* 𝓞_ℂ_[p]) : Logarithm.PeriodRings.BdRPlus p ≃+* Logarithm.PeriodRings.BdRPlus p :=
  RingEquiv.ofRingHom (bdRPlusMap p f.toRingHom) (bdRPlusMap p f.symm.toRingHom)
    (by rw [← bdRPlusMap_comp]; simpa using bdRPlusMap_id p)
    (by rw [← bdRPlusMap_comp]; simpa using bdRPlusMap_id p)

def coefficientAction : (𝓞_ℂ_[p] ≃+* 𝓞_ℂ_[p]) →* (Logarithm.PeriodRings.BdRPlus p ≃+* Logarithm.PeriodRings.BdRPlus p) where
  toFun := bdRPlusEquiv p
  map_one' := by
    apply RingEquiv.toRingHom_injective
    exact bdRPlusMap_id p
  map_mul' f g := by
    apply RingEquiv.toRingHom_injective
    exact bdRPlusMap_comp p f.toRingHom g.toRingHom

/-- The Galois action on the coefficient ring satisfies the group laws. -/
def galoisIntegerAction : PeriodInvariants.PeriodRing.PadicGalois p →* (𝓞_ℂ_[p] ≃+* 𝓞_ℂ_[p]) where
  toFun := PeriodInvariants.PeriodRing.galoisIntegerEquiv p
  map_one' := by
    apply RingEquiv.ext
    intro x
    apply Subtype.ext
    change UniformSpace.Completion.mapRingHom (RingHom.id (PadicAlgCl p)) continuous_id
      (x : ℂ_[p]) = (x : ℂ_[p])
    rw [UniformSpace.Completion.mapRingHom_id]
    rfl
  map_mul' σ τ := by
    apply RingEquiv.ext
    intro x
    apply Subtype.ext
    change UniformSpace.Completion.mapRingHom
        (σ.toRingEquiv.toRingHom.comp τ.toRingEquiv.toRingHom)
        ((PeriodInvariants.PeriodRing.algebraicGalois_isometry p σ).continuous.comp
          (PeriodInvariants.PeriodRing.algebraicGalois_isometry p τ).continuous) (x : ℂ_[p]) =
      UniformSpace.Completion.mapRingHom σ.toRingEquiv.toRingHom
        (PeriodInvariants.PeriodRing.algebraicGalois_isometry p σ).continuous
        (UniformSpace.Completion.mapRingHom τ.toRingEquiv.toRingHom
          (PeriodInvariants.PeriodRing.algebraicGalois_isometry p τ).continuous (x : ℂ_[p]))
    exact (congrArg (fun h : ℂ_[p] →+* ℂ_[p] => h (x : ℂ_[p]))
      (UniformSpace.Completion.mapRingHom_comp
        (f := τ.toRingEquiv.toRingHom) (g := σ.toRingEquiv.toRingHom)
        (PeriodInvariants.PeriodRing.algebraicGalois_isometry p σ).continuous
        (PeriodInvariants.PeriodRing.algebraicGalois_isometry p τ).continuous)).symm

/-- The actual absolute Galois action on B_dR^+ as a group homomorphism. -/
def galoisBdRPlusAction : PeriodInvariants.PeriodRing.PadicGalois p →* (Logarithm.PeriodRings.BdRPlus p ≃+* Logarithm.PeriodRings.BdRPlus p) :=
  (coefficientAction p).comp (galoisIntegerAction p)

theorem galoisBdRPlusAction_preserves_filtration (σ : PeriodInvariants.PeriodRing.PadicGalois p) (n : ℕ) :
    (positiveFiltration p n).map (galoisBdRPlusAction p σ).toRingHom ≤
      positiveFiltration p n :=
  bdRPlusMap_preserves_filtration p (PeriodInvariants.PeriodRing.galoisIntegerEquiv p σ).toRingHom n

/-- Every filtration step is Galois-stable, with equality supplied by the inverse action. -/
theorem galoisBdRPlusAction_filtration (σ : PeriodInvariants.PeriodRing.PadicGalois p) (n : ℕ) :
    (positiveFiltration p n).map (galoisBdRPlusAction p σ).toRingHom =
      positiveFiltration p n := by
  apply le_antisymm (galoisBdRPlusAction_preserves_filtration p σ n)
  have hcomp : (galoisBdRPlusAction p σ).toRingHom.comp
      (galoisBdRPlusAction p σ⁻¹).toRingHom = RingHom.id _ := by
    have he : galoisBdRPlusAction p σ * galoisBdRPlusAction p σ⁻¹ = 1 := by
      rw [← map_mul, mul_inv_cancel, map_one]
    exact congrArg RingEquiv.toRingHom he
  calc
    positiveFiltration p n =
        ((positiveFiltration p n).map (galoisBdRPlusAction p σ⁻¹).toRingHom).map
          (galoisBdRPlusAction p σ).toRingHom := by
      rw [Ideal.map_map, hcomp, Ideal.map_id]
    _ ≤ (positiveFiltration p n).map (galoisBdRPlusAction p σ).toRingHom :=
      Ideal.map_mono (galoisBdRPlusAction_preserves_filtration p σ⁻¹ n)

end

end OAI.NumberTheory.PadicHodge.WeakAdmissibility.DeRham
