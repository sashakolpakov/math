import OAI.Geometry.ComplexBall.QuotientCompact
import OAI.Geometry.ComplexBall.Congruence

/-! # Free -/

namespace OAI.Geometry.ComplexBall.Free.ArithmeticQuotient

noncomputable section

section

/-! Properly discontinuous torsion-free actions are free. -/

open scoped Classical
open _root_.Topology OAI.Geometry.ComplexBall.ArithmeticQuotientEquationsData

lemma free_of_properlyDiscontinuous_torsionFree {G X : Type*} [Group G]
    [TopologicalSpace X] [MulAction G X] [ProperlyDiscontinuousSMul G X]
    (ht : ∀ g : G, ∀ k : ℕ, 0 < k → g ^ k = 1 → g = 1) : IsCancelSMul G X := by
  apply isCancelSMul_iff_eq_one_of_smul_eq.mpr
  intro g x hg
  let : Finite (MulAction.stabilizer G x) :=
    (ProperlyDiscontinuousSMul.finite_stabilizer (Γ := G) x).to_subtype
  let s : MulAction.stabilizer G x := ⟨g, hg⟩
  obtain ⟨k, hk, hpow⟩ := (isOfFinOrder_of_finite s).exists_pow_eq_one
  exact ht g k hk (congrArg Subtype.val hpow)

variable {E : Type*} [Field E] [NumberField E] [NumberField.IsCMField E]

lemma principalUnitary_torsionFree (b : E) (N : ℕ)
    (ht : ∀ g : ArithmeticQuotientEquationsData.Mat E, ArithmeticQuotientEquationsData.principalLevel b N g → ∀ k : ℕ, 0 < k → g ^ k = 1 → g = 1) :
    ∀ g : Congruence.ArithmeticQuotient.principalUnitarySubgroup b N, ∀ k : ℕ, 0 < k → g ^ k = 1 → g = 1 := by
  intro g k hk hpow
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  exact ht g.val.val.val ((Congruence.ArithmeticQuotient.mem_principalUnitarySubgroup b N g.val).mp g.property) k hk
    (congrArg (fun x : Congruence.ArithmeticQuotient.principalUnitarySubgroup b N => x.val.val.val) hpow)

lemma principalImage_torsionFree (b : E) (N : ℕ) (μ : E →+* ℂ)
    (ht : ∀ g : ArithmeticQuotientEquationsData.Mat E, ArithmeticQuotientEquationsData.principalLevel b N g → ∀ k : ℕ, 0 < k → g ^ k = 1 → g = 1) :
    ∀ g : (Congruence.ArithmeticQuotient.principalUnitarySubgroup b N).map (ArithmeticQuotientEquationsData.infinitePlaceMap b μ),
      ∀ k : ℕ, 0 < k → g ^ k = 1 → g = 1 := by
  intro g k hk hpow
  obtain ⟨x, hx, he⟩ := g.property
  have hpow' : (ArithmeticQuotientEquationsData.infinitePlaceMap b μ x) ^ k = 1 := by
    rw [he]
    exact congrArg Subtype.val hpow
  have hxpow : x ^ k = 1 := by
    apply ArithmeticQuotientEquationsData.infinitePlaceMap_injective b μ
    simpa only [map_pow, map_one] using hpow'
  have hxone := principalUnitary_torsionFree b N ht ⟨x, hx⟩ k hk (Subtype.ext hxpow)
  apply Subtype.ext
  rw [← he]
  have heq : x = 1 := congrArg Subtype.val hxone
  rw [heq, map_one]
  rfl

end

/-! The negative-vector quotient is homeomorphic to the ball orbit quotient.
Its relation includes both the arithmetic matrix action and nonzero scalars. -/

open scoped Classical
open _root_.Topology OAI.Geometry.ComplexBall.ArithmeticQuotientEquationsData

variable (b : ℂ) (Γ : Subgroup (ArithmeticQuotientEquationsData.SU (starRingEnd ℂ) b))

def coneOrbitSetoid : Setoid (ArithmeticQuotientBoostBall.Cone b) := (MulAction.orbitRel Γ (ArithmeticQuotientBoostBall.Ball b)).comap (ArithmeticQuotientBoostBall.normalize b)

def coneQuotientToBall : Quotient (coneOrbitSetoid b Γ) → MulAction.orbitRel.Quotient Γ (ArithmeticQuotientBoostBall.Ball b) :=
  Quotient.map (ArithmeticQuotientBoostBall.normalize b) (fun _ _ h => h)

def ballQuotientToCone : MulAction.orbitRel.Quotient Γ (ArithmeticQuotientBoostBall.Ball b) → Quotient (coneOrbitSetoid b Γ) :=
  Quotient.map (ArithmeticQuotientBoostBall.liftBall b) (by
    intro z w h
    change (MulAction.orbitRel Γ (ArithmeticQuotientBoostBall.Ball b)) (ArithmeticQuotientBoostBall.normalize b (ArithmeticQuotientBoostBall.liftBall b z)) (ArithmeticQuotientBoostBall.normalize b (ArithmeticQuotientBoostBall.liftBall b w))
    simpa only [ArithmeticQuotientBoostBall.normalize_lift] using h)

def coneQuotientHomeomorph : Quotient (coneOrbitSetoid b Γ) ≃ₜ MulAction.orbitRel.Quotient Γ (ArithmeticQuotientBoostBall.Ball b) where
  toFun := coneQuotientToBall b Γ
  invFun := ballQuotientToCone b Γ
  left_inv q := by
    induction q using Quotient.inductionOn with
    | h z =>
      apply Quotient.sound
      change (MulAction.orbitRel Γ (ArithmeticQuotientBoostBall.Ball b)) (ArithmeticQuotientBoostBall.normalize b (ArithmeticQuotientBoostBall.liftBall b (ArithmeticQuotientBoostBall.normalize b z))) (ArithmeticQuotientBoostBall.normalize b z)
      rw [ArithmeticQuotientBoostBall.normalize_lift]
  right_inv q := by
    induction q using Quotient.inductionOn with
    | h z =>
      change Quotient.mk _ (ArithmeticQuotientBoostBall.normalize b (ArithmeticQuotientBoostBall.liftBall b z)) = Quotient.mk _ z
      rw [ArithmeticQuotientBoostBall.normalize_lift]
  continuous_toFun := (ArithmeticQuotientBoostBall.continuous_normalize b).quotient_map' _
  continuous_invFun := (ArithmeticQuotientBoostBall.continuous_liftBall b).quotient_map' _

lemma coneOrbitSetoid_iff_scalar (z w : ArithmeticQuotientBoostBall.Cone b) :
    (coneOrbitSetoid b Γ).r z w ↔
      ∃ γ : Γ, ∃ t : ℂ, t ≠ 0 ∧ w.val = t • (γ.val • z).val := by
  constructor
  · intro h
    have hh := (MulAction.orbitRel Γ (ArithmeticQuotientBoostBall.Ball b)).symm h
    obtain ⟨γ, hγ⟩ := hh
    have hn : ArithmeticQuotientBoostBall.normalize b (γ.val • z) = ArithmeticQuotientBoostBall.normalize b w := by
      rw [ArithmeticQuotientBoostBall.normalize_equivariant]
      exact hγ
    exact ⟨γ, (ArithmeticQuotientBoostBall.normalize_eq_iff_scalar b _ _).mp hn⟩
  · rintro ⟨γ, t, ht, he⟩
    have hn := (ArithmeticQuotientBoostBall.normalize_eq_iff_scalar b (γ.val • z) w).mpr ⟨t, ht, he⟩
    apply (MulAction.orbitRel Γ (ArithmeticQuotientBoostBall.Ball b)).symm
    refine ⟨γ, ?_⟩
    exact (ArithmeticQuotientBoostBall.normalize_equivariant b γ.val z).symm.trans hn

variable {E : Type*} [Field E] [NumberField E] [NumberField.IsCMField E]

lemma coneOrbitSetoid_principal_iff (b : E) (μ : E →+* ℂ) (N : ℕ)
    (z w : ArithmeticQuotientEquationsData.NegativeVectors b μ) :
    (coneOrbitSetoid (μ b) ((Congruence.ArithmeticQuotient.principalUnitarySubgroup b N).map (ArithmeticQuotientEquationsData.infinitePlaceMap b μ))).r z w ↔
      ArithmeticQuotientEquationsData.orbitRelation b μ N z w := by
  refine (coneOrbitSetoid_iff_scalar (μ b)
    ((Congruence.ArithmeticQuotient.principalUnitarySubgroup b N).map (ArithmeticQuotientEquationsData.infinitePlaceMap b μ)) z w).trans ?_
  constructor
  · rintro ⟨γ, t, ht, he⟩
    obtain ⟨g, hg, hγ⟩ := γ.property
    refine ⟨g.val.val, (Congruence.ArithmeticQuotient.mem_principalUnitarySubgroup b N g).mp hg, t, ht, ?_⟩
    intro i
    have hi := congrArg (fun x : ArithmeticQuotientEquationsData.Vec ℂ => x i) he
    rw [← hγ] at hi
    exact hi
  · rintro ⟨g, hg, t, ht, he⟩
    let s : ArithmeticQuotientEquationsData.RationalSU b := ⟨⟨g, hg.1⟩, hg.2.1⟩
    have hs : s ∈ Congruence.ArithmeticQuotient.principalUnitarySubgroup b N := (Congruence.ArithmeticQuotient.mem_principalUnitarySubgroup b N s).mpr hg
    let γ : (Congruence.ArithmeticQuotient.principalUnitarySubgroup b N).map (ArithmeticQuotientEquationsData.infinitePlaceMap b μ) :=
      ⟨ArithmeticQuotientEquationsData.infinitePlaceMap b μ s, ⟨s, hs, rfl⟩⟩
    refine ⟨γ, t, ht, ?_⟩
    funext i
    exact he i

end

end OAI.Geometry.ComplexBall.Free.ArithmeticQuotient
