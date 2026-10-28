import OAI.NumberTheory.PadicHodge.IntegralComparison.DividedPower.Transfer

/-! # Power Envelope -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.DividedPower.PowerEnvelope

noncomputable section

/-!
# IntegralComparison: a universal divided-power envelope

The construction uses finite expressions in ring operations and divided
powers of ideal expressions. Equality means equality under every compatible
evaluation into a divided-power ring. The expression set bounds the size
of the resulting ring; no universal envelope is assumed as an interface.
-/

universe u

mutual
  inductive Expression (B : Type u) [CommRing B] (I : Ideal B) : Type u
    | constant : B → Expression B I
    | add : Expression B I → Expression B I → Expression B I
    | neg : Expression B I → Expression B I
    | mul : Expression B I → Expression B I → Expression B I
    | ideal : IdealExpression B I → Expression B I

  inductive IdealExpression (B : Type u) [CommRing B] (I : Ideal B) : Type u
    | base : I → IdealExpression B I
    | add : IdealExpression B I → IdealExpression B I → IdealExpression B I
    | neg : IdealExpression B I → IdealExpression B I
    | mul : Expression B I → IdealExpression B I → IdealExpression B I
    | dpow : (n : ℕ) → n ≠ 0 → IdealExpression B I → IdealExpression B I
end

variable (A B : Type u) [CommRing A] [CommRing B]
variable (J : Ideal A) (δ : DividedPowers J) (f : A →+* B) (I : Ideal B)

/-- A compatible target for the relative divided-power envelope. -/
structure Target where
  ring : Type u
  [commRing : CommRing ring]
  ideal : Ideal ring
  dividedPowers : DividedPowers ideal
  fromBase : B →+* ring
  mapsIdeal : I ≤ ideal.comap fromBase
  baseCompatible : DividedPowers.IsDPMorphism δ dividedPowers (fromBase.comp f)

attribute [instance] Target.commRing

variable {A B J δ f I}

mutual
  def evaluate (M : Target A B J δ f I) : Expression B I → M.ring
    | .constant b => M.fromBase b
    | .add x y => evaluate M x + evaluate M y
    | .neg x => -evaluate M x
    | .mul x y => evaluate M x * evaluate M y
    | .ideal x => evaluateIdeal M x

  def evaluateIdeal (M : Target A B J δ f I) : IdealExpression B I → M.ring
    | .base b => M.fromBase b
    | .add x y => evaluateIdeal M x + evaluateIdeal M y
    | .neg x => -evaluateIdeal M x
    | .mul x y => evaluate M x * evaluateIdeal M y
    | .dpow n _ x => M.dividedPowers.dpow n (evaluateIdeal M x)
end

lemma evaluateIdeal_mem (M : Target A B J δ f I) :
    ∀ x : IdealExpression B I, evaluateIdeal M x ∈ M.ideal
  | .base b => M.mapsIdeal b.property
  | .add x y => M.ideal.add_mem (evaluateIdeal_mem M x) (evaluateIdeal_mem M y)
  | .neg x => M.ideal.neg_mem (evaluateIdeal_mem M x)
  | .mul x y => M.ideal.mul_mem_left (evaluate M x) (evaluateIdeal_mem M y)
  | .dpow _n hn x => M.dividedPowers.dpow_mem hn (evaluateIdeal_mem M x)

variable (A B J δ f I)

abbrev Evaluations := ∀ M : Target A B J δ f I, M.ring

def value (x : Expression B I) : Evaluations A B J δ f I :=
  fun M => evaluate M x

/-- The subring consisting of evaluations of finite expressions. -/
def expressionRing : Subring (Evaluations A B J δ f I) where
  carrier := Set.range (value A B J δ f I)
  zero_mem' := ⟨.constant 0, funext fun M => map_zero M.fromBase⟩
  one_mem' := ⟨.constant 1, funext fun M => map_one M.fromBase⟩
  add_mem' := by
    rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩
    exact ⟨.add x y, rfl⟩
  neg_mem' := by
    rintro _ ⟨x, rfl⟩
    exact ⟨.neg x, rfl⟩
  mul_mem' := by
    rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩
    exact ⟨.mul x y, rfl⟩

def element (x : Expression B I) : expressionRing A B J δ f I :=
  ⟨value A B J δ f I x, x, rfl⟩

lemma element_surjective : Function.Surjective (element A B J δ f I) := by
  intro x
  obtain ⟨e, he⟩ := x.property
  exact ⟨e, Subtype.ext he⟩

instance expressionRing_small : Small.{u} (expressionRing A B J δ f I) :=
  small_of_surjective (element_surjective A B J δ f I)

/-- Evaluation at each target, as an actual ring homomorphism. -/
def evaluation (M : Target A B J δ f I) : expressionRing A B J δ f I →+* M.ring :=
  (Pi.evalRingHom (fun M : Target A B J δ f I => M.ring) M).comp
    (expressionRing A B J δ f I).subtype

lemma evaluations_separate (x y : expressionRing A B J δ f I)
    (h : ∀ M, evaluation A B J δ f I M x = evaluation A B J δ f I M y) : x = y :=
  Subtype.ext (funext h)

/-- The original ring maps to the constant expressions. -/
def fromBase : B →+* expressionRing A B J δ f I where
  toFun b := element A B J δ f I (.constant b)
  map_zero' := by apply evaluations_separate; intro M; exact map_zero M.fromBase
  map_one' := by apply evaluations_separate; intro M; exact map_one M.fromBase
  map_add' b c := by apply evaluations_separate; intro M; exact map_add M.fromBase b c
  map_mul' b c := by apply evaluations_separate; intro M; exact map_mul M.fromBase b c

/-- The ideal consists of the values of ideal expressions. -/
def expressionIdeal : Ideal (expressionRing A B J δ f I) where
  carrier := Set.range (fun x : IdealExpression B I => element A B J δ f I (.ideal x))
  zero_mem' := by
    refine ⟨.base ⟨0, I.zero_mem⟩, ?_⟩
    apply evaluations_separate
    intro M
    exact map_zero M.fromBase
  add_mem' := by
    rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩
    exact ⟨.add x y, rfl⟩
  smul_mem' := by
    rintro x _ ⟨y, rfl⟩
    obtain ⟨e, rfl⟩ := element_surjective A B J δ f I x
    exact ⟨.mul e y, rfl⟩

lemma evaluation_mapsIdeal (M : Target A B J δ f I) :
    expressionIdeal A B J δ f I ≤ M.ideal.comap (evaluation A B J δ f I M) := by
  rintro _ ⟨x, rfl⟩
  exact evaluateIdeal_mem M x

lemma dividedPower_preimage (n : ℕ) {x : expressionRing A B J δ f I}
    (hx : x ∈ expressionIdeal A B J δ f I) :
    ∃ y : expressionRing A B J δ f I,
      (n ≠ 0 → y ∈ expressionIdeal A B J δ f I) ∧
      ∀ M, evaluation A B J δ f I M y =
        M.dividedPowers.dpow n (evaluation A B J δ f I M x) := by
  obtain ⟨e, rfl⟩ := hx
  by_cases hn : n = 0
  · subst n
    refine ⟨1, by simp, ?_⟩
    intro M
    exact (M.dividedPowers.dpow_zero (evaluateIdeal_mem M e)).symm
  · refine ⟨element A B J δ f I (.ideal (.dpow n hn e)), ?_, fun _ => rfl⟩
    exact fun _ => ⟨.dpow n hn e, rfl⟩

/-- Divided powers on the expression ideal, proved by all target evaluations. -/
def expressionDividedPowers : DividedPowers (expressionIdeal A B J δ f I) :=
  Transfer.dividedPowers
    (expressionIdeal A B J δ f I)
    (fun M : Target A B J δ f I => M.ideal) (fun M : Target A B J δ f I => M.dividedPowers)
    (evaluation A B J δ f I) (evaluations_separate A B J δ f I)
    (evaluation_mapsIdeal A B J δ f I) (dividedPower_preimage A B J δ f I)

lemma evaluation_dpow (M : Target A B J δ f I) (n : ℕ)
    {x : expressionRing A B J δ f I} (hx : x ∈ expressionIdeal A B J δ f I) :
    evaluation A B J δ f I M ((expressionDividedPowers A B J δ f I).dpow n x) =
      M.dividedPowers.dpow n (evaluation A B J δ f I M x) :=
  Transfer.dividedPowers_map
    (expressionIdeal A B J δ f I)
    (fun M : Target A B J δ f I => M.ideal) (fun M : Target A B J δ f I => M.dividedPowers)
    (evaluation A B J δ f I) (evaluations_separate A B J δ f I)
    (evaluation_mapsIdeal A B J δ f I) (dividedPower_preimage A B J δ f I) n hx M

/-- Every compatible target receives an actual divided-power morphism. -/
def evaluationDP (M : Target A B J δ f I) :
    DividedPowers.DPMorphism (expressionDividedPowers A B J δ f I) M.dividedPowers where
  toRingHom := evaluation A B J δ f I M
  ideal_comp := Ideal.map_le_iff_le_comap.mpr (evaluation_mapsIdeal A B J δ f I M)
  dpow_comp _ hx := (evaluation_dpow A B J δ f I M _ hx).symm

lemma fromBase_mapsIdeal : I ≤ (expressionIdeal A B J δ f I).comap (fromBase A B J δ f I) :=
  fun x hx => ⟨.base ⟨x, hx⟩, rfl⟩

lemma expression_baseCompatible (hf : J ≤ I.comap f) :
    DividedPowers.IsDPMorphism δ (expressionDividedPowers A B J δ f I)
      ((fromBase A B J δ f I).comp f) := by
  refine ⟨Ideal.map_le_iff_le_comap.mpr (fun x hx => ?_), ?_⟩
  · exact fromBase_mapsIdeal A B J δ f I (hf hx)
  · intro n x hx
    apply evaluations_separate
    intro M
    simp only [RingHom.comp_apply]
    rw [evaluation_dpow A B J δ f I M n (fromBase_mapsIdeal A B J δ f I (hf hx))]
    exact M.baseCompatible.2 x hx

lemma dpow_idealElement (n : ℕ) (hn : n ≠ 0) (e : IdealExpression B I) :
    (expressionDividedPowers A B J δ f I).dpow n (element A B J δ f I (.ideal e)) =
      element A B J δ f I (.ideal (.dpow n hn e)) := by
  apply evaluations_separate
  intro M
  exact evaluation_dpow A B J δ f I M n ⟨e, rfl⟩

section UniversalProperty

variable (M : Target A B J δ f I) (g : expressionRing A B J δ f I →+* M.ring)
variable (hg : DividedPowers.IsDPMorphism (expressionDividedPowers A B J δ f I)
  M.dividedPowers g)
variable (hbase : g.comp (fromBase A B J δ f I) = M.fromBase)

mutual
  private theorem hom_element (hg : DividedPowers.IsDPMorphism (expressionDividedPowers A B J δ f I)
      M.dividedPowers g) (hbase : g.comp (fromBase A B J δ f I) = M.fromBase) : ∀ e : Expression B I,
      g (element A B J δ f I e) = evaluate M e
    | .constant b => DFunLike.congr_fun hbase b
    | .add x y => by
      change g (element A B J δ f I x + element A B J δ f I y) = _
      rw [map_add, hom_element hg hbase x,
        hom_element hg hbase y]
      rfl
    | .neg x => by
      change g (-element A B J δ f I x) = _
      rw [map_neg, hom_element hg hbase x]
      rfl
    | .mul x y => by
      change g (element A B J δ f I x * element A B J δ f I y) = _
      rw [map_mul, hom_element hg hbase x,
        hom_element hg hbase y]
      rfl
    | .ideal e => hom_idealElement hg hbase e

  private theorem hom_idealElement (hg : DividedPowers.IsDPMorphism (expressionDividedPowers A B J δ f I)
      M.dividedPowers g) (hbase : g.comp (fromBase A B J δ f I) = M.fromBase) : ∀ e : IdealExpression B I,
      g (element A B J δ f I (.ideal e)) = evaluateIdeal M e
    | .base b => DFunLike.congr_fun hbase b.val
    | .add x y => by
      change g (element A B J δ f I (.ideal x) + element A B J δ f I (.ideal y)) = _
      rw [map_add, hom_idealElement hg hbase x,
        hom_idealElement hg hbase y]
      rfl
    | .neg x => by
      change g (-element A B J δ f I (.ideal x)) = _
      rw [map_neg, hom_idealElement hg hbase x]
      rfl
    | .mul x y => by
      change g (element A B J δ f I x * element A B J δ f I (.ideal y)) = _
      rw [map_mul, hom_element hg hbase x,
        hom_idealElement hg hbase y]
      rfl
    | .dpow n hn x => by
      rw [← dpow_idealElement A B J δ f I n hn x, ← hg.2 _ ⟨x, rfl⟩,
        hom_idealElement hg hbase x]
      rfl
end

include hg hbase

/-- Uniqueness of the morphism to each compatible divided-power ring. -/
lemma evaluation_unique : g = evaluation A B J δ f I M := by
  ext x
  obtain ⟨e, rfl⟩ := element_surjective A B J δ f I x
  exact hom_element A B J δ f I M g hg hbase e

end UniversalProperty

/-- A small coordinate ring for the divided-power envelope. -/
def Envelope := Shrink.{u} (expressionRing A B J δ f I)

/-- Use one ring instance on the envelope, so its ideals, quotient rings,
and divided powers all use the same inherited operations. -/
instance envelopeCommRing : CommRing (Envelope A B J δ f I) :=
  inferInstanceAs (CommRing (Shrink.{u} (expressionRing A B J δ f I)))

def envelopeEquiv : Envelope A B J δ f I ≃+* expressionRing A B J δ f I :=
  Shrink.ringEquiv _

def envelopeIdeal : Ideal (Envelope A B J δ f I) :=
  (expressionIdeal A B J δ f I).map (envelopeEquiv A B J δ f I).symm.toRingHom

def envelopeDividedPowers : DividedPowers (envelopeIdeal A B J δ f I) :=
  DividedPowers.ofRingEquiv
    (e := (envelopeEquiv A B J δ f I).symm) rfl (expressionDividedPowers A B J δ f I)

def toEnvelope : B →+* Envelope A B J δ f I :=
  (envelopeEquiv A B J δ f I).symm.toRingHom.comp (fromBase A B J δ f I)

lemma toEnvelope_mapsIdeal : I ≤ (envelopeIdeal A B J δ f I).comap (toEnvelope A B J δ f I) :=
  fun _x hx => Ideal.mem_map_of_mem _ (fromBase_mapsIdeal A B J δ f I hx)

private def shrinkDP : DividedPowers.DPMorphism
    (expressionDividedPowers A B J δ f I) (envelopeDividedPowers A B J δ f I) where
  toRingHom := (envelopeEquiv A B J δ f I).symm.toRingHom
  ideal_comp := le_rfl
  dpow_comp _ _ := DividedPowers.ofRingEquiv_dpow_apply _ _

/-- The constructed envelope is a compatible target, with its ring in the
same universe as the input rings. -/
def envelopeTarget (hf : J ≤ I.comap f) : Target A B J δ f I where
  ring := Envelope A B J δ f I
  ideal := envelopeIdeal A B J δ f I
  dividedPowers := envelopeDividedPowers A B J δ f I
  fromBase := toEnvelope A B J δ f I
  mapsIdeal := toEnvelope_mapsIdeal A B J δ f I
  baseCompatible := (shrinkDP A B J δ f I).isDPMorphism.comp _
    (expression_baseCompatible A B J δ f I hf)

private def unshrinkDP : DividedPowers.DPMorphism
    (envelopeDividedPowers A B J δ f I) (expressionDividedPowers A B J δ f I) where
  toRingHom := (envelopeEquiv A B J δ f I).toRingHom
  ideal_comp := by
    apply Ideal.map_le_iff_le_comap.mpr
    intro x hx
    obtain ⟨y, hy, rfl⟩ :=
      (Ideal.mem_map_iff_of_surjective _ (envelopeEquiv A B J δ f I).symm.surjective).mp hx
    change (envelopeEquiv A B J δ f I) ((envelopeEquiv A B J δ f I).symm y) ∈
      expressionIdeal A B J δ f I
    simpa only [RingEquiv.apply_symm_apply] using hy
  dpow_comp x _ := by
    change (expressionDividedPowers A B J δ f I).dpow _ ((envelopeEquiv A B J δ f I) x) =
      (envelopeEquiv A B J δ f I) ((envelopeEquiv A B J δ f I).symm
        ((expressionDividedPowers A B J δ f I).dpow _ ((envelopeEquiv A B J δ f I) x)))
    exact ((envelopeEquiv A B J δ f I).apply_symm_apply _).symm

/-- The universal map from the small divided-power envelope to a target. -/
def lift (M : Target A B J δ f I) :
    DividedPowers.DPMorphism (envelopeDividedPowers A B J δ f I) M.dividedPowers :=
  (evaluationDP A B J δ f I M).comp (unshrinkDP A B J δ f I)

lemma lift_fromBase (M : Target A B J δ f I) :
    (lift A B J δ f I M).toRingHom.comp (toEnvelope A B J δ f I) = M.fromBase := by
  ext b
  change evaluation A B J δ f I M ((envelopeEquiv A B J δ f I)
    ((envelopeEquiv A B J δ f I).symm (fromBase A B J δ f I b))) = M.fromBase b
  rw [RingEquiv.apply_symm_apply]
  rfl

lemma lift_unique (M : Target A B J δ f I)
    (g : DividedPowers.DPMorphism (envelopeDividedPowers A B J δ f I) M.dividedPowers)
    (hbase : g.toRingHom.comp (toEnvelope A B J δ f I) = M.fromBase) :
    g = lift A B J δ f I M := by
  have h := evaluation_unique A B J δ f I M
    (g.toRingHom.comp (envelopeEquiv A B J δ f I).symm.toRingHom)
    (g.isDPMorphism.comp _ (shrinkDP A B J δ f I).isDPMorphism) hbase
  apply DFunLike.ext
  intro x
  obtain ⟨y, rfl⟩ := (envelopeEquiv A B J δ f I).symm.surjective x
  have hy := DFunLike.congr_fun h y
  change g ((envelopeEquiv A B J δ f I).symm y) = evaluation A B J δ f I M
    ((envelopeEquiv A B J δ f I) ((envelopeEquiv A B J δ f I).symm y))
  rw [RingEquiv.apply_symm_apply]
  exact hy

/-- The universal property is proved for all compatible targets. -/
lemma existsUnique_lift (M : Target A B J δ f I) :
    ∃! g : DividedPowers.DPMorphism (envelopeDividedPowers A B J δ f I) M.dividedPowers,
      g.toRingHom.comp (toEnvelope A B J δ f I) = M.fromBase :=
  ⟨lift A B J δ f I M, lift_fromBase A B J δ f I M,
    fun g hg => lift_unique A B J δ f I M g hg⟩

/-- Compose a compatible target with an actual divided-power morphism. -/
def postcomposeTarget (M : Target A B J δ f I) {R : Type u} [CommRing R]
    {K : Ideal R} (ε : DividedPowers K) (g : DividedPowers.DPMorphism M.dividedPowers ε) :
    Target A B J δ f I where
  ring := R
  ideal := K
  dividedPowers := ε
  fromBase := g.toRingHom.comp M.fromBase
  mapsIdeal := fun _x hx => g.ideal_comp (Ideal.mem_map_of_mem _ (M.mapsIdeal hx))
  baseCompatible := g.isDPMorphism.comp _ M.baseCompatible

lemma lift_postcompose (M : Target A B J δ f I) {R : Type u} [CommRing R]
    {K : Ideal R} (ε : DividedPowers K) (g : DividedPowers.DPMorphism M.dividedPowers ε) :
    g.comp (lift A B J δ f I M) = lift A B J δ f I (postcomposeTarget A B J δ f I M ε g) := by
  apply lift_unique A B J δ f I (postcomposeTarget A B J δ f I M ε g)
  change g.toRingHom.comp ((lift A B J δ f I M).toRingHom.comp (toEnvelope A B J δ f I)) =
    g.toRingHom.comp M.fromBase
  rw [lift_fromBase]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.DividedPower.PowerEnvelope
