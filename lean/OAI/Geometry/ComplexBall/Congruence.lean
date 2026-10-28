import OAI.Geometry.ComplexBall.IntegralLattice
import OAI.Geometry.ComplexBall.Levels

/-! # Congruence -/

namespace OAI.Geometry.ComplexBall.Congruence.ArithmeticQuotient

noncomputable section

section

/-! Integral unitary matrices and the stabilizer of the actual O_E lattice. -/

open scoped Classical _root_.NumberField BigOperators
open OAI.Geometry.ComplexBall.ArithmeticQuotientEquationsData _root_.NumberField

section Basic
variable {E : Type*} [Field E] [NumberField E] [IsCMField E]

def integralUnitarySubgroup (b : E) : Subgroup (ArithmeticQuotientEquationsData.RationalSU b) where
  carrier := {g | ∀ i j, IsIntegral ℤ (g.val i j)}
  one_mem' := by
    intro i j
    change IsIntegral ℤ ((1 : ArithmeticQuotientEquationsData.Mat E) i j)
    by_cases h : i = j
    · simpa only [Matrix.one_apply, ite_eq_left h] using (isIntegral_one : IsIntegral ℤ (1 : E))
    · simpa only [Matrix.one_apply, ite_eq_right h] using (isIntegral_zero : IsIntegral ℤ (0 : E))
  mul_mem' := by
    intro g h hg hh i j
    change IsIntegral ℤ (∑ k, g.val i k * h.val k j)
    exact IsIntegral.sum _ (fun k _ => (hg i k).mul (hh k j))
  inv_mem' := by
    intro g hg
    exact Levels.ArithmeticQuotient.integral_adjugate g.val.val hg

end Basic

section Realization
variable {E : Type} [Field E] [NumberField E] [IsCMField E]

lemma integralUnitary_stabilizes (b : E) (g : ArithmeticQuotientEquationsData.RationalSU b) :
    g ∈ integralUnitarySubgroup b ↔ ∀ x : ArithmeticQuotientEquationsData.Vec E,
      Matrix.SpecialLinearGroup.toLin' g.val x ∈ IntegralLattice.ArithmeticQuotient.integralVectorModule (E := E) ↔
        x ∈ IntegralLattice.ArithmeticQuotient.integralVectorModule (E := E) := by
  constructor
  · intro hg x
    constructor
    · intro hx
      have hi := Levels.ArithmeticQuotient.integral_mulVec g.val.val.adjugate (Levels.ArithmeticQuotient.integral_adjugate g.val.val hg)
        (g.val.val.mulVec x) ((NumberTheory.ArithmeticGroups.Lattice.CongruenceLevel.mem_standardLattice _).mp hx)
      have he : g.val.val.adjugate.mulVec (g.val.val.mulVec x) = x := by
        change Matrix.SpecialLinearGroup.toLin' g.val⁻¹ (Matrix.SpecialLinearGroup.toLin' g.val x) = x
        rw [← LinearEquiv.mul_apply, ← map_mul, inv_mul_cancel, map_one]
        rfl
      rw [he] at hi
      exact (NumberTheory.ArithmeticGroups.Lattice.CongruenceLevel.mem_standardLattice _).mpr hi
    · intro hx
      exact (NumberTheory.ArithmeticGroups.Lattice.CongruenceLevel.mem_standardLattice _).mpr
        (Levels.ArithmeticQuotient.integral_mulVec g.val.val hg x ((NumberTheory.ArithmeticGroups.Lattice.CongruenceLevel.mem_standardLattice _).mp hx))
  · intro h i j
    have hx : Pi.single j (1 : E) ∈ IntegralLattice.ArithmeticQuotient.integralVectorModule (E := E) := by
      apply (NumberTheory.ArithmeticGroups.Lattice.CongruenceLevel.mem_standardLattice _).mpr
      intro k
      by_cases hk : k = j
      · simpa only [Pi.single_apply, ite_eq_left hk] using (isIntegral_one : IsIntegral ℤ (1 : E))
      · simpa only [Pi.single_apply, ite_eq_right hk] using (isIntegral_zero : IsIntegral ℤ (0 : E))
    have hi := (NumberTheory.ArithmeticGroups.Lattice.CongruenceLevel.mem_standardLattice _).mp ((h _).mpr hx) i
    simpa [Matrix.SpecialLinearGroup.toLin'_apply, Matrix.toLin'_apply] using hi

lemma cmCoordinates_mem_lattice (δ : E) (hδ : IsCMField.complexConj E δ = -δ)
    (hδ0 : δ ≠ 0) (x : ArithmeticQuotientEquationsData.Vec E) :
    IntegralLattice.ArithmeticQuotient.cmCoordinates δ hδ hδ0 x ∈ (IntegralLattice.ArithmeticQuotient.cmIntegralLattice δ hδ hδ0).module ↔
      x ∈ IntegralLattice.ArithmeticQuotient.integralVectorModule (E := E) := by
  change IntegralLattice.ArithmeticQuotient.cmCoordinates δ hδ hδ0 x ∈ (IntegralLattice.ArithmeticQuotient.integralVectorModule (E := E)).map _ ↔ _
  constructor
  · rintro ⟨y, hy, he⟩
    exact (IntegralLattice.ArithmeticQuotient.cmCoordinates δ hδ hδ0).injective he ▸ hy
  · intro hx
    exact ⟨x, hx, rfl⟩

lemma integralUnitary_map_stabilizer (b : E) (hb : IsCMField.complexConj E b = b)
    (δ : E) (hδ : IsCMField.complexConj E δ = -δ) (hδ0 : δ ≠ 0) :
    (integralUnitarySubgroup b).map (ArithmeticQuotientSplitUnitary.originalUnitaryRationalEquiv b hb δ hδ hδ0).toMonoidHom =
      (ArithmeticQuotientSplitUnitary.originalUnitaryAlgebraicGroup b hb δ hδ).latticeStabilizer (IntegralLattice.ArithmeticQuotient.cmIntegralLattice δ hδ hδ0) := by
  ext g
  obtain ⟨g, rfl⟩ := (ArithmeticQuotientSplitUnitary.originalUnitaryRationalEquiv b hb δ hδ hδ0).surjective g
  rw [Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply, integralUnitary_stabilizes]
  change (∀ x : ArithmeticQuotientEquationsData.Vec E, Matrix.SpecialLinearGroup.toLin' g.val x ∈ IntegralLattice.ArithmeticQuotient.integralVectorModule (E := E) ↔
    x ∈ IntegralLattice.ArithmeticQuotient.integralVectorModule (E := E)) ↔ ∀ y : Fin 6 → ArithmeticQuotientEquationsData.RealField E,
    Matrix.SpecialLinearGroup.toLin' (ArithmeticQuotientSplitUnitary.originalUnitaryRationalEquiv b hb δ hδ hδ0 g).val y ∈
      (IntegralLattice.ArithmeticQuotient.cmIntegralLattice δ hδ hδ0).module ↔ y ∈ (IntegralLattice.ArithmeticQuotient.cmIntegralLattice δ hδ hδ0).module
  constructor
  · intro h y
    obtain ⟨x, rfl⟩ := (IntegralLattice.ArithmeticQuotient.cmCoordinates δ hδ hδ0).surjective y
    rw [← IntegralLattice.ArithmeticQuotient.cmCoordinates_action, cmCoordinates_mem_lattice, cmCoordinates_mem_lattice]
    exact h x
  · intro h x
    have he := h (IntegralLattice.ArithmeticQuotient.cmCoordinates δ hδ hδ0 x)
    rw [← IntegralLattice.ArithmeticQuotient.cmCoordinates_action, cmCoordinates_mem_lattice, cmCoordinates_mem_lattice] at he
    exact he

end Realization

variable {E : Type*} [Field E] [NumberField E] [IsCMField E]

def integralUnitaryMatrix (b : E) : integralUnitarySubgroup b →* ArithmeticQuotientEquationsData.SL (𝓞 E) where
  toFun g := ⟨fun i j => ⟨g.val.val i j, g.property i j⟩, by
    apply RingOfIntegers.coe_injective
    exact ((algebraMap (𝓞 E) E).map_det
      (fun i j : Fin 3 => (⟨g.val.val i j, g.property i j⟩ : 𝓞 E))).trans g.val.val.property⟩
  map_one' := by
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    apply Subtype.ext
    change (1 : ArithmeticQuotientEquationsData.Mat E) i j = ((1 : ArithmeticQuotientEquationsData.Mat (𝓞 E)) i j : E)
    by_cases h : i = j <;> simp [Matrix.one_apply, h]
  map_mul' g h := by
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    apply Subtype.ext
    change (∑ k, g.val.val i k * h.val.val k j) =
      (algebraMap (𝓞 E) E) (∑ k, (⟨g.val.val i k, g.property i k⟩ : 𝓞 E) *
        (⟨h.val.val k j, h.property k j⟩ : 𝓞 E))
    exact (map_sum (algebraMap (𝓞 E) E)
      (fun k : Fin 3 => (⟨g.val.val i k, g.property i k⟩ : 𝓞 E) *
        (⟨h.val.val k j, h.property k j⟩ : 𝓞 E)) Finset.univ).symm

end

/-! The exact principal matrix congruence group is a finite-index subgroup
of the integral unitary group, by reduction modulo the nonzero integer N. -/

open scoped Classical _root_.NumberField
open OAI.Geometry.ComplexBall.ArithmeticQuotientEquationsData _root_.NumberField

variable {E : Type*} [Field E] [NumberField E] [IsCMField E]

def levelIdeal (N : ℕ) : Ideal (𝓞 E) := Ideal.span {(N : 𝓞 E)}

def integralReduction (b : E) (N : ℕ) :
    integralUnitarySubgroup b →* ArithmeticQuotientEquationsData.SL (𝓞 E ⧸ levelIdeal (E := E) N) :=
  (Matrix.SpecialLinearGroup.map (Ideal.Quotient.mk _)).comp (integralUnitaryMatrix b)

def principalUnitarySubgroup (b : E) (N : ℕ) : Subgroup (ArithmeticQuotientEquationsData.RationalSU b) :=
  (integralReduction b N).ker.map (integralUnitarySubgroup b).subtype

lemma principalUnitary_le_integral (b : E) (N : ℕ) :
    principalUnitarySubgroup b N ≤ integralUnitarySubgroup b := by
  rintro g ⟨h, _, rfl⟩
  exact h.property

omit [NumberField E] [IsCMField E] in
lemma levelQuotient_eq_iff (N : ℕ) (a c : 𝓞 E) :
    Ideal.Quotient.mk (levelIdeal N) a = Ideal.Quotient.mk (levelIdeal N) c ↔
      ∃ y : 𝓞 E, (a : E) - (c : E) = (N : E) * (y : E) := by
  rw [Ideal.Quotient.mk_eq_mk_iff_sub_mem]
  change a - c ∈ Ideal.span {(N : 𝓞 E)} ↔ _
  rw [Ideal.mem_span_singleton]
  constructor
  · rintro ⟨y, hy⟩
    exact ⟨y, congrArg (algebraMap (𝓞 E) E) hy⟩
  · rintro ⟨y, hy⟩
    exact ⟨y, RingOfIntegers.coe_injective hy⟩

lemma integralReduction_mem_ker (b : E) (N : ℕ) (g : integralUnitarySubgroup b) :
    g ∈ (integralReduction b N).ker ↔
      ∃ B : ArithmeticQuotientEquationsData.Mat (𝓞 E), ∀ i j, g.val.val i j - (1 : ArithmeticQuotientEquationsData.Mat E) i j = (N : E) * (B i j : E) := by
  rw [MonoidHom.mem_ker, Matrix.SpecialLinearGroup.ext_iff]
  have hi (i j : Fin 3) :
      ((1 : ArithmeticQuotientEquationsData.Mat (𝓞 E)) i j : E) = (1 : ArithmeticQuotientEquationsData.Mat E) i j := by
    by_cases h : i = j <;> simp [Matrix.one_apply, h]
  constructor
  · intro h
    have he (i j : Fin 3) : ∃ y : 𝓞 E,
        g.val.val i j - (1 : ArithmeticQuotientEquationsData.Mat E) i j = (N : E) * (y : E) := by
      have hj := h i j
      change Ideal.Quotient.mk (levelIdeal N) (⟨g.val.val i j, g.property i j⟩ : 𝓞 E) =
        (1 : ArithmeticQuotientEquationsData.Mat (𝓞 E ⧸ levelIdeal N)) i j at hj
      have hq : Ideal.Quotient.mk (levelIdeal (E := E) N) ((1 : ArithmeticQuotientEquationsData.Mat (𝓞 E)) i j) =
          (1 : ArithmeticQuotientEquationsData.Mat (𝓞 E ⧸ levelIdeal N)) i j := by
        by_cases hh : i = j <;> simp [Matrix.one_apply, hh]
      obtain ⟨y, hy⟩ := (levelQuotient_eq_iff N
        (⟨g.val.val i j, g.property i j⟩ : 𝓞 E) ((1 : ArithmeticQuotientEquationsData.Mat (𝓞 E)) i j)).mp (hj.trans hq.symm)
      refine ⟨y, ?_⟩
      change g.val.val i j - ((1 : ArithmeticQuotientEquationsData.Mat (𝓞 E)) i j : E) = (N : E) * (y : E) at hy
      rw [hi] at hy
      exact hy
    choose B hB using he
    exact ⟨B, hB⟩
  · rintro ⟨B, hB⟩ i j
    change Ideal.Quotient.mk (levelIdeal N) (⟨g.val.val i j, g.property i j⟩ : 𝓞 E) =
      (1 : ArithmeticQuotientEquationsData.Mat (𝓞 E ⧸ levelIdeal N)) i j
    have hq : Ideal.Quotient.mk (levelIdeal (E := E) N) ((1 : ArithmeticQuotientEquationsData.Mat (𝓞 E)) i j) =
        (1 : ArithmeticQuotientEquationsData.Mat (𝓞 E ⧸ levelIdeal N)) i j := by
      by_cases hh : i = j <;> simp [Matrix.one_apply, hh]
    apply Eq.trans _ hq
    apply (levelQuotient_eq_iff N _ _).mpr
    refine ⟨B i j, ?_⟩
    change g.val.val i j - ((1 : ArithmeticQuotientEquationsData.Mat (𝓞 E)) i j : E) = (N : E) * (B i j : E)
    rw [hi]
    exact hB i j

lemma mem_principalUnitarySubgroup (b : E) (N : ℕ) (g : ArithmeticQuotientEquationsData.RationalSU b) :
    g ∈ principalUnitarySubgroup b N ↔ ArithmeticQuotientEquationsData.principalLevel b N g.val.val := by
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact ⟨g.val.val.property, g.val.property, (integralReduction_mem_ker b N g).mp hg⟩
  · intro hg
    let g' : integralUnitarySubgroup b := ⟨g, Levels.ArithmeticQuotient.principal_entries_integral b N g.val.val hg⟩
    exact ⟨g', (integralReduction_mem_ker b N g').mpr hg.2.2, rfl⟩

lemma principalUnitary_commensurable (b : E) (N : ℕ) (hN : 0 < N) :
    (principalUnitarySubgroup b N).Commensurable (integralUnitarySubgroup b) := by
  have hN0 : (N : 𝓞 E) ≠ 0 := by exact_mod_cast hN.ne'
  have hI : levelIdeal (E := E) N ≠ ⊥ := by
    intro h
    apply hN0
    have hm : (N : 𝓞 E) ∈ levelIdeal (E := E) N := Ideal.subset_span (Set.mem_singleton _)
    rw [h] at hm
    exact hm
  let : Finite (𝓞 E ⧸ levelIdeal (E := E) N) := Ring.HasFiniteQuotients.finiteQuotient hI
  have hker : (integralReduction b N).ker.FiniteIndex := inferInstance
  refine ⟨?_, ?_⟩
  · have he : (principalUnitarySubgroup b N).relIndex (integralUnitarySubgroup b) =
        (integralReduction b N).ker.index := by
      change ((integralReduction b N).ker.map (integralUnitarySubgroup b).subtype).relIndex _ = _
      have ht : (⊤ : Subgroup (integralUnitarySubgroup b)).map
          (integralUnitarySubgroup b).subtype = integralUnitarySubgroup b := by
        exact (MonoidHom.range_eq_map _).symm.trans (Subgroup.range_subtype _)
      calc
        _ = ((integralReduction b N).ker.map (integralUnitarySubgroup b).subtype).relIndex
            ((⊤ : Subgroup (integralUnitarySubgroup b)).map (integralUnitarySubgroup b).subtype) :=
          congrArg (fun H => ((integralReduction b N).ker.map (integralUnitarySubgroup b).subtype).relIndex H) ht.symm
        _ = (integralReduction b N).ker.relIndex ⊤ :=
          Subgroup.relIndex_map_map_of_injective _ _ Subtype.val_injective
        _ = _ := by simp
    exact ⟨he.symm ▸ hker.index_ne_zero⟩
  · refine ⟨?_⟩
    rw [Subgroup.relIndex_eq_one.mpr (principalUnitary_le_integral b N)]
    decide

end

end OAI.Geometry.ComplexBall.Congruence.ArithmeticQuotient
