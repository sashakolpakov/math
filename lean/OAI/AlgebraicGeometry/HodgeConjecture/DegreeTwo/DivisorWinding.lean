import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.DivisorEquations
import OAI.AlgebraicGeometry.DivisorClass.Chern.Rational.SectionWinding

/-! # Divisor Winding -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.HodgeConjecture.DegreeTwo.DivisorWinding.Constructions

/-!
# DegreeTwo: evaluation of the actual rational-section power equation

An equality in the function field can be evaluated wherever its parameter
does not vanish. Clearing denominators proves this also for negative orders.
Applied to the actual section-coordinate unit, it gives the analytic power
equation with exactly the algebraic divisor multiplicity.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

/-- Integer-power identities in an embedded function field persist under
every field-valued evaluation where the denominator is nonzero. -/
theorem evaluate_integer_power_relation {R K C : Type*} [CommRing R] [Field K] [Field C]
    (ι : R →+* K) (hι : Function.Injective ι) (φ : R →+* C)
    (s v p : R) (m : ℤ) (he : ι s = ι v * (ι p) ^ m) (hp : φ p ≠ 0) :
    φ s = φ v * (φ p) ^ m := by
  have hpR : p ≠ 0 := fun h => hp (h ▸ φ.map_zero)
  have hpK : ι p ≠ 0 := (map_ne_zero_iff ι hι).mpr hpR
  cases m with
  | ofNat n =>
      rw [Int.ofNat_eq_natCast, zpow_natCast, ← map_pow, ← map_mul] at he
      rw [hι he, map_mul, map_pow, Int.ofNat_eq_natCast, zpow_natCast]
  | negSucc n =>
      rw [zpow_negSucc, ← div_eq_mul_inv] at he ⊢
      apply (eq_div_iff (pow_ne_zero (n + 1) hp)).mpr
      have h := (eq_div_iff (pow_ne_zero (n + 1) hpK)).mp he
      rw [← map_pow, ← map_mul] at h
      have hφ := congrArg φ (hι h)
      simpa only [map_mul, map_pow] using hφ

/-- A parameter of nonzero order cannot vanish under an evaluation where
both the rational section and its extending unit are nonzero. -/
theorem integer_power_parameter_nonzero {R K C : Type*} [CommRing R] [Field K] [Field C]
    (ι : R →+* K) (hι : Function.Injective ι) (φ : R →+* C)
    (s v p : R) (m : ℤ) (hm : m ≠ 0) (hp : ι p ≠ 0)
    (he : ι s = ι v * (ι p) ^ m) (hs : φ s ≠ 0) (hv : φ v ≠ 0) : φ p ≠ 0 := by
  intro hz
  cases m with
  | ofNat n =>
      have hn : n ≠ 0 := by intro hn; exact hm (by simp [hn])
      rw [Int.ofNat_eq_natCast, zpow_natCast, ← map_pow, ← map_mul] at he
      have hφ := congrArg φ (hι he)
      rw [map_mul, map_pow, hz, zero_pow hn, mul_zero] at hφ
      exact hs hφ
  | negSucc n =>
      rw [zpow_negSucc, ← div_eq_mul_inv] at he
      have h := (eq_div_iff (pow_ne_zero (n + 1) hp)).mp he
      rw [← map_pow, ← map_mul] at h
      have hφ := congrArg φ (hι h)
      rw [map_mul, map_pow, hz, zero_pow (Nat.succ_ne_zero n), mul_zero] at hφ
      exact hv hφ.symm

namespace DivisorEvaluation

variable {X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation} (L : DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle X) [IsIntegral X.carrier]

def sectionEvaluationHom (U : X.carrier.Opens) (y : DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen X U) : Γ(X.carrier, U) →+* ℂ :=
  (DivisorClass.Chern.AnalyticTransitions.Construction.globalSectionEvaluation ((DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.openPointHomeomorph X U).symm y)).comp U.topIso.inv.hom

omit [IsIntegral X.carrier] in
theorem sectionEvaluationHom_apply (U : X.carrier.Opens) (y : DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen X U) (s : Γ(X.carrier, U)) :
    sectionEvaluationHom (X := X) U y s = DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn X U s y := rfl

/-- The actual rational-section coordinate evaluates as its regular unit
times the parameter raised to the same integer power, including pole order. -/
theorem referenceEquation_power (i : X.carrier) (U : X.carrier.Opens) [Nonempty U]
    (hi : U ≤ L.trivializingOpen i) (p : Γ(X.carrier, U)) (v : Γ(X.carrier, U)ˣ) (m : ℤ)
    (he : (L.rationalSectionCoordinate i : X.carrier.functionField) =
      X.carrier.germToFunctionField U v * (X.carrier.germToFunctionField U p) ^ m)
    (y : L.referenceLocus U) (hp : DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn X U p y.val ≠ 0) :
    L.referenceEquation i U hi y = DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn X U (v : Γ(X.carrier, U)) y.val *
      (DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn X U p y.val) ^ m := by
  let W := U ⊓ L.rationalReferenceOpen
  let z : DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen X W := L.referenceLocusIntersectionMap U y
  let : Nonempty W := ⟨⟨ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying z.val, z.property⟩⟩
  let hWU : W ≤ U := inf_le_left
  let t : Γ(X.carrier, W) :=
    L.ambientTransitionOn i (genericPoint X.carrier) W (hWU.trans hi) inf_le_right
  let q : Γ(X.carrier, W) := X.carrier.presheaf.map (homOfLE hWU).op p
  let w : Γ(X.carrier, W) := X.carrier.presheaf.map (homOfLE hWU).op (v : Γ(X.carrier, U))
  have hc := congrArg Units.val (L.referenceEquation_genericCoordinate i U hi)
  have hfield : X.carrier.germToFunctionField W t =
      X.carrier.germToFunctionField W w * (X.carrier.germToFunctionField W q) ^ m := by
    change X.carrier.germToFunctionField W t =
      X.carrier.germToFunctionField W (X.carrier.presheaf.map (homOfLE hWU).op (v : Γ(X.carrier, U))) *
        (X.carrier.germToFunctionField W (X.carrier.presheaf.map (homOfLE hWU).op p)) ^ m
    rw [DivisorClass.Chern.Rational.Coordinates.Construction.germToFunctionField_restrict, DivisorClass.Chern.Rational.Coordinates.Construction.germToFunctionField_restrict]
    exact hc.trans he
  have hp' : sectionEvaluationHom (X := X) W z q ≠ 0 := by
    change DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn X W (X.carrier.presheaf.map (homOfLE hWU).op p) z ≠ 0
    rw [DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn_restrict]
    exact hp
  have hv := evaluate_integer_power_relation (X.carrier.germToFunctionField W).hom
    (X.carrier.germToFunctionField_injective W) (sectionEvaluationHom (X := X) W z)
    t w q m hfield hp'
  change L.referenceEquation i U hi y =
    DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn X W (X.carrier.presheaf.map (homOfLE hWU).op (v : Γ(X.carrier, U))) z *
      (DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn X W (X.carrier.presheaf.map (homOfLE hWU).op p) z) ^ m at hv
  rw [DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn_restrict, DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn_restrict] at hv
  exact hv

/-- Every codimension-one point admits an actual regular local equation
whose analytic power is the previously defined algebraic divisor order. -/
theorem rationalSection_analytic_local_equation (x : X.carrier) (hx : Order.coheight x = 1)
    (i : X.carrier) (hxi : x ∈ L.trivializingOpen i) :
    ∃ (U : X.carrier.Opens) (_ : U ∈ X.carrier.affineOpens) (hxU : x ∈ U)
      (hUi : U ≤ L.trivializingOpen i) (p : Γ(X.carrier, U)) (v : Γ(X.carrier, U)ˣ),
      Irreducible (X.carrier.presheaf.germ U x hxU p) ∧
      ∀ y : L.referenceLocus U, DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn X U p y.val ≠ 0 →
        L.referenceEquation i U hUi y = DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn X U (v : Γ(X.carrier, U)) y.val *
          (DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn X U p y.val) ^ (L.rationalSectionOrder x) := by
  obtain ⟨U, hU, hxU, hUi, p, v, hp, he⟩ := DivisorEquations.Constructions.rationalSection_local_equation L x hx i hxi
  let : Nonempty U := ⟨⟨x, hxU⟩⟩
  exact ⟨U, hU, hxU, hUi, p, v, hp,
    fun y hy => referenceEquation_power L i U hUi p v (L.rationalSectionOrder x) he y hy⟩

end DivisorEvaluation

end AlgebraicGeometry.HodgeConjecture.DegreeTwo.DivisorWinding.Constructions

namespace AlgebraicGeometry.HodgeConjecture.DegreeTwo.DivisorWinding.Constructions.DivisorEvaluation

/-!
# DegreeTwo: actual algebraic divisor multiplicity in supported winding

For nonzero order, the local parameter cannot vanish where the rational
section and its extending unit are both nonzero. The proved analytic power
equation therefore gives the actual integer multiple in relative cohomology.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

variable {X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation} (L : DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle X) [IsIntegral X.carrier]

/-- At nonzero order the regular parameter is nonvanishing on the reference
locus, as a consequence of the actual function-field identity. -/
theorem referenceParameter_ne_zero (i : X.carrier) (U : X.carrier.Opens) [Nonempty U]
    (hi : U ≤ L.trivializingOpen i) (p : Γ(X.carrier, U)) (hp : p ≠ 0)
    (v : Γ(X.carrier, U)ˣ) (m : ℤ) (hm : m ≠ 0)
    (he : (L.rationalSectionCoordinate i : X.carrier.functionField) =
      X.carrier.germToFunctionField U v * (X.carrier.germToFunctionField U p) ^ m)
    (y : L.referenceLocus U) : DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn X U p y.val ≠ 0 := by
  let W := U ⊓ L.rationalReferenceOpen
  let z : DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen X W := L.referenceLocusIntersectionMap U y
  let : Nonempty W := ⟨⟨ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying z.val, z.property⟩⟩
  let hWU : W ≤ U := inf_le_left
  let t : Γ(X.carrier, W)ˣ :=
    L.ambientTransitionOn i (genericPoint X.carrier) W (hWU.trans hi) inf_le_right
  let q : Γ(X.carrier, W) := X.carrier.presheaf.map (homOfLE hWU).op p
  let w : Γ(X.carrier, W)ˣ := Units.map (X.carrier.presheaf.map (homOfLE hWU).op).hom.toMonoidHom v
  have hc := congrArg Units.val (L.referenceEquation_genericCoordinate i U hi)
  have hfield : X.carrier.germToFunctionField W t =
      X.carrier.germToFunctionField W w * (X.carrier.germToFunctionField W q) ^ m := by
    change X.carrier.germToFunctionField W t =
      X.carrier.germToFunctionField W (X.carrier.presheaf.map (homOfLE hWU).op (v : Γ(X.carrier, U))) *
        (X.carrier.germToFunctionField W (X.carrier.presheaf.map (homOfLE hWU).op p)) ^ m
    rw [DivisorClass.Chern.Rational.Coordinates.Construction.germToFunctionField_restrict, DivisorClass.Chern.Rational.Coordinates.Construction.germToFunctionField_restrict]
    exact hc.trans he
  have hpW : X.carrier.germToFunctionField W q ≠ 0 := by
    change X.carrier.germToFunctionField W (X.carrier.presheaf.map (homOfLE hWU).op p) ≠ 0
    rw [DivisorClass.Chern.Rational.Coordinates.Construction.germToFunctionField_restrict]
    exact (map_ne_zero_iff _ (X.carrier.germToFunctionField_injective U)).mpr hp
  have hy := integer_power_parameter_nonzero (X.carrier.germToFunctionField W).hom
    (X.carrier.germToFunctionField_injective W) (sectionEvaluationHom (X := X) W z)
    t w q m hm hpW hfield (t.isUnit.map _).ne_zero (w.isUnit.map _).ne_zero
  change DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn X W (X.carrier.presheaf.map (homOfLE hWU).op p) z ≠ 0 at hy
  rw [DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn_restrict] at hy
  exact hy

def referenceParameter (U : X.carrier.Opens) (p : Γ(X.carrier, U)) : C(L.referenceLocus U, ℂ) :=
  (DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn X U p).comp ⟨Subtype.val, continuous_subtype_val⟩

/-- The actual local relative class has its algebraic integer multiplicity;
the extending regular unit contributes zero by exactness. -/
theorem rationalSectionLocalSupportedClass_power (i : X.carrier) (U : X.carrier.Opens) [Nonempty U]
    (hi : U ≤ L.trivializingOpen i) (p : Γ(X.carrier, U)) (hp : p ≠ 0)
    (v : Γ(X.carrier, U)ˣ) (m : ℤ) (hm : m ≠ 0)
    (he : (L.rationalSectionCoordinate i : X.carrier.functionField) =
      X.carrier.germToFunctionField U v * (X.carrier.germToFunctionField U p) ^ m) :
    L.rationalSectionLocalSupportedClass i U hi =
      m • DivisorClass.Chern.Supported.Winding.supportedWindingClass (TopCat.of (DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen X U)) (L.referenceLocus U)
        (referenceParameter L U p) (referenceParameter_ne_zero L i U hi p hp v m hm he) := by
  apply DivisorClass.Chern.Supported.Winding.supportedWindingClass_unit_power (TopCat.of (DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen X U)) (L.referenceLocus U)
    (referenceParameter L U p) (L.referenceEquation i U hi)
    (referenceParameter_ne_zero L i U hi p hp v m hm he) (L.referenceEquation_ne_zero i U hi)
    (DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn X U (v : Γ(X.carrier, U))) (DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn_unit_ne_zero X U v) m
  intro y
  exact (referenceEquation_power L i U hi p v m he y
    (referenceParameter_ne_zero L i U hi p hp v m hm he y)).trans (mul_comm _ _)

/-- At an actual nonzero divisor coefficient, choose the regular parameter
and obtain that exact coefficient in the actual local supported class. -/
theorem rationalSection_local_winding_multiplicity (x : X.carrier) (hx : Order.coheight x = 1)
    (hm : L.rationalSectionOrder x ≠ 0) (i : X.carrier) (hxi : x ∈ L.trivializingOpen i) :
    ∃ (U : X.carrier.Opens) (_ : U ∈ X.carrier.affineOpens) (hxU : x ∈ U)
      (hUi : U ≤ L.trivializingOpen i) (p : Γ(X.carrier, U)),
      Irreducible (X.carrier.presheaf.germ U x hxU p) ∧
      ∃ hp : ∀ y, referenceParameter L U p y ≠ 0,
        L.rationalSectionLocalSupportedClass i U hUi =
          (L.rationalSectionOrder x) • DivisorClass.Chern.Supported.Winding.supportedWindingClass (TopCat.of (DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen X U))
            (L.referenceLocus U) (referenceParameter L U p) hp := by
  obtain ⟨U, hU, hxU, hUi, p, v, hp, he⟩ := DivisorEquations.Constructions.rationalSection_local_equation L x hx i hxi
  let : Nonempty U := ⟨⟨x, hxU⟩⟩
  have hp0 : p ≠ 0 := by
    intro h
    apply hp.ne_zero
    rw [h, map_zero]
  exact ⟨U, hU, hxU, hUi, p, hp,
    referenceParameter_ne_zero L i U hUi p hp0 v (L.rationalSectionOrder x) hm he,
    rationalSectionLocalSupportedClass_power L i U hUi p hp0 v (L.rationalSectionOrder x) hm he⟩

/-- If the actual rational coordinate extends as a regular unit, its local
supported class vanishes by the native relative exact sequence. -/
theorem rationalSectionLocalSupportedClass_unit_zero (i : X.carrier) (U : X.carrier.Opens)
    [Nonempty U] (hi : U ≤ L.trivializingOpen i) (v : Γ(X.carrier, U)ˣ)
    (he : (L.rationalSectionCoordinate i : X.carrier.functionField) = X.carrier.germToFunctionField U v) :
    L.rationalSectionLocalSupportedClass i U hi = 0 := by
  have heq : L.referenceEquation i U hi =
      (DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn X U (v : Γ(X.carrier, U))).comp ⟨Subtype.val, continuous_subtype_val⟩ := by
    apply ContinuousMap.ext
    intro y
    have hp := DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn_unit_ne_zero X U (1 : Γ(X.carrier, U)ˣ) y.val
    have hfield : (L.rationalSectionCoordinate i : X.carrier.functionField) =
        X.carrier.germToFunctionField U v * (X.carrier.germToFunctionField U (1 : Γ(X.carrier, U))) ^ (0 : ℤ) := by
      simpa only [zpow_zero, mul_one] using he
    have hy := referenceEquation_power L i U hi 1 v 0 hfield y hp
    change L.referenceEquation i U hi y = DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn X U (v : Γ(X.carrier, U)) y.val
    simpa only [zpow_zero, mul_one] using hy
  unfold DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.rationalSectionLocalSupportedClass
  exact (DivisorClass.Chern.Supported.Winding.supportedWindingClass_congr _ _ _ _ (L.referenceEquation_ne_zero i U hi)
    (fun y => DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn_unit_ne_zero X U v y.val) heq).trans
      (DivisorClass.Chern.Supported.Winding.supportedWindingClass_extending_unit (TopCat.of (DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen X U)) (L.referenceLocus U)
        (DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn X U (v : Γ(X.carrier, U))) (DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn_unit_ne_zero X U v))

/-- A zero algebraic divisor coefficient gives actual local supported
vanishing on an affine neighborhood of the codimension-one point. -/
theorem rationalSection_local_zero_of_order_zero (x : X.carrier) (hx : Order.coheight x = 1)
    (hm : L.rationalSectionOrder x = 0) (i : X.carrier) (hxi : x ∈ L.trivializingOpen i) :
    ∃ (U : X.carrier.Opens) (_ : U ∈ X.carrier.affineOpens) (_ : x ∈ U)
      (hUi : U ≤ L.trivializingOpen i), L.rationalSectionLocalSupportedClass i U hUi = 0 := by
  obtain ⟨U, hU, hxU, hUi, p, v, _, he⟩ := DivisorEquations.Constructions.rationalSection_local_equation L x hx i hxi
  let : Nonempty U := ⟨⟨x, hxU⟩⟩
  rw [hm, zpow_zero, mul_one] at he
  exact ⟨U, hU, hxU, hUi, rationalSectionLocalSupportedClass_unit_zero L i U hUi v he⟩

end AlgebraicGeometry.HodgeConjecture.DegreeTwo.DivisorWinding.Constructions.DivisorEvaluation

end

end OAI
