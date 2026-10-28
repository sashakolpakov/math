import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Data
import Mathlib.NumberTheory.NumberField.FractionalIdeal
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.NumberTheory.Padics.RingHoms
import OAI.AlgebraicGeometry.AbelianScheme.CentralAction.Marking

/-! # Side Residues -/

namespace OAI.AlgebraicGeometry.AbelianScheme.CentralAction.SideResidues.Construction

noncomputable section

section

/-! Residue coordinates constructed from TateComparison's actual split completion.
Tensor induction supplies simultaneous integral lifts; no weak approximation
or extra prime-coordinate compatibility is assumed. -/

open scoped TensorProduct
open _root_.NumberField

open OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Data

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]

def residueCoordinates (D : TateComparison.Data.SphericalPELAlbaneseData E K s q) (h : ℕ) :
    𝓞 E →+* (Fin s × Bool → ZMod (q ^ h)) :=
  RingHom.pi (fun v => (PadicInt.toZModPow h).comp (D.localCharacter v))

theorem tensor_residue_lift (D : TateComparison.Data.SphericalPELAlbaneseData E K s q) (h : ℕ)
    (t : ℤ_[q] ⊗[ℤ] 𝓞 E) :
    ∃ b : 𝓞 E, ∀ v : Fin s × Bool,
      residueCoordinates D h b v = PadicInt.toZModPow h (D.localCompletionMap t v) := by
  induction t using TensorProduct.inductionOn with
  | tmul z b =>
    refine ⟨((PadicInt.toZModPow h z).val : 𝓞 E) * b, ?_⟩
    intro v
    have ht : D.localCompletionMap (z ⊗ₜ[ℤ] b) v = z * D.localCharacter v b := by
      change ((algebraMap ℤ_[q] (Fin s × Bool → ℤ_[q])).toIntAlgHom z *
        (RingHom.pi D.localCharacter).toIntAlgHom b) v = _
      rfl
    rw [ht]
    change PadicInt.toZModPow h
      (D.localCharacter v (((PadicInt.toZModPow h z).val : 𝓞 E) * b)) = _
    rw [map_mul, map_natCast, map_mul, map_natCast, ZMod.natCast_val, map_mul]
    simp only [ZMod.cast_id]
  | add t u ht hu =>
    obtain ⟨b, hb⟩ := ht
    obtain ⟨c, hc⟩ := hu
    refine ⟨b + c, ?_⟩
    intro v
    simp only [map_add, Pi.add_apply, hb v, hc v]

/-- Every tuple of split residue classes has an O_E representative. -/
theorem residueCoordinates_surjective (D : TateComparison.Data.SphericalPELAlbaneseData E K s q)
    (hgood : D.IsGoodCompletelySplitPrime) (h : ℕ) :
    Function.Surjective (residueCoordinates D h) := by
  intro y
  let z : Fin s × Bool → ℤ_[q] := fun v => (y v).val
  obtain ⟨t, ht⟩ := hgood.1.2 z
  obtain ⟨b, hb⟩ := tensor_residue_lift D h t
  refine ⟨b, ?_⟩
  funext v
  rw [hb, ht]
  simp [z]

def qPowerIdeal (E : Type*) [Field E] (q h : ℕ) : Ideal (𝓞 E) :=
  Ideal.span {((q ^ h : ℕ) : 𝓞 E)}

theorem qPowerIdeal_le_residue_kernel (D : TateComparison.Data.SphericalPELAlbaneseData E K s q) (h : ℕ) :
    qPowerIdeal E q h ≤ RingHom.ker (residueCoordinates D h) := by
  apply Ideal.span_le.mpr
  intro b hb
  obtain rfl := Set.mem_singleton_iff.mp hb
  change residueCoordinates D h ((q ^ h : ℕ) : 𝓞 E) = 0
  funext v
  change PadicInt.toZModPow h (D.localCharacter v ((q ^ h : ℕ) : 𝓞 E)) = 0
  rw [map_natCast, map_natCast]
  exact ZMod.natCast_self _

/-- There are exactly the prescribed split residue coordinates: the
kernel is q^h O_E. Surjectivity and the integral-basis rank prove this,
without assuming a separate prime factorization interface. -/
theorem residueCoordinates_kernel (D : TateComparison.Data.SphericalPELAlbaneseData E K s q)
    (hgood : D.IsGoodCompletelySplitPrime)
    (hdegree : Module.finrank ℚ E = 2 * s) (h : ℕ) :
    RingHom.ker (residueCoordinates D h) = qPowerIdeal E q h := by
  let I := qPowerIdeal E q h
  have hI : ∀ b : 𝓞 E, b ∈ I → residueCoordinates D h b = 0 :=
    fun b hb => qPowerIdeal_le_residue_kernel D h hb
  let f : (𝓞 E ⧸ I) →+* (Fin s × Bool → ZMod (q ^ h)) :=
    Ideal.Quotient.lift I (residueCoordinates D h) hI
  have hf : Function.Surjective f :=
    Ideal.Quotient.lift_surjective_of_surjective I hI (residueCoordinates_surjective D hgood h)
  let : Finite (𝓞 E ⧸ I) :=
    Marking.Construction.finite_level_ring E (q ^ h) (pow_pos (Fact.out : q.Prime).pos h)
  let : Fintype (𝓞 E ⧸ I) := Fintype.ofFinite _
  have hcard : Fintype.card (𝓞 E ⧸ I) =
      Fintype.card (Fin s × Bool → ZMod (q ^ h)) := by
    calc
      Fintype.card (𝓞 E ⧸ I) = Ideal.absNorm I := Nat.card_eq_fintype_card.symm
      _ = (q ^ h) ^ Module.finrank ℤ (𝓞 E) := Ideal.absNorm_span_natCast (q ^ h)
      _ = (q ^ h) ^ (s * 2) := by rw [RingOfIntegers.rank, hdegree, Nat.mul_comm 2 s]
      _ = Fintype.card (Fin s × Bool → ZMod (q ^ h)) := by simp
  have hi : Function.Injective f :=
    ((Fintype.bijective_iff_surjective_and_card f).mpr ⟨hf, hcard⟩).1
  apply le_antisymm ?_ (qPowerIdeal_le_residue_kernel D h)
  intro b hb
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  apply hi
  change residueCoordinates D h b = f 0
  rw [map_zero]
  exact hb

end

section

/-! The one-side-per-pair ideals are defined from the actual residue
coordinates. Their product with the conjugate ideal is proved to be (q).
This is the ideal to which Finiteness is applied for C0. -/

open _root_.NumberField

open OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Data

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]

def selectedResidues (D : TateComparison.Data.SphericalPELAlbaneseData E K s q) (side : Fin s → Bool) :
    𝓞 E →+* (Fin s → ZMod (q ^ 1)) where
  toFun b v := residueCoordinates D 1 b (v, side v)
  map_one' := by ext v; exact congrFun (map_one (residueCoordinates D 1)) (v, side v)
  map_zero' := by ext v; exact congrFun (map_zero (residueCoordinates D 1)) (v, side v)
  map_add' b c := by ext v; exact congrFun (map_add (residueCoordinates D 1) b c) (v, side v)
  map_mul' b c := by ext v; exact congrFun (map_mul (residueCoordinates D 1) b c) (v, side v)

def sideIdeal (D : TateComparison.Data.SphericalPELAlbaneseData E K s q) (side : Fin s → Bool) : Ideal (𝓞 E) :=
  RingHom.ker (selectedResidues D side)

theorem mem_sideIdeal (D : TateComparison.Data.SphericalPELAlbaneseData E K s q)
    (side : Fin s → Bool) (b : 𝓞 E) :
    b ∈ sideIdeal D side ↔ ∀ v, residueCoordinates D 1 b (v, side v) = 0 := by
  change (fun v => residueCoordinates D 1 b (v, side v)) = 0 ↔ _
  exact funext_iff

theorem sideIdeal_inf_opposite (D : TateComparison.Data.SphericalPELAlbaneseData E K s q)
    (hgood : D.IsGoodCompletelySplitPrime)
    (hdegree : Module.finrank ℚ E = 2 * s) (side : Fin s → Bool) :
    sideIdeal D side ⊓ sideIdeal D (fun v => !(side v)) = qPowerIdeal E q 1 := by
  rw [← residueCoordinates_kernel D hgood hdegree 1]
  ext b
  change (b ∈ sideIdeal D side ∧ b ∈ sideIdeal D (fun v => !(side v))) ↔
    residueCoordinates D 1 b = 0
  rw [mem_sideIdeal, mem_sideIdeal]
  constructor
  · rintro ⟨hl, hr⟩
    funext ⟨v, w⟩
    have hlv := hl v
    have hrv := hr v
    cases hs : side v <;> cases w <;> simp_all
  · intro hb
    constructor <;> intro v <;> simp [hb]

theorem sideIdeal_sup_opposite (D : TateComparison.Data.SphericalPELAlbaneseData E K s q)
    (hgood : D.IsGoodCompletelySplitPrime) (side : Fin s → Bool) :
    sideIdeal D side ⊔ sideIdeal D (fun v => !(side v)) = ⊤ := by
  classical
  let y : Fin s × Bool → ZMod (q ^ 1) :=
    fun v => if v.2 = side v.1 then 0 else 1
  obtain ⟨b, hb⟩ := residueCoordinates_surjective D hgood 1 y
  have hl : b ∈ sideIdeal D side := by
    rw [mem_sideIdeal]
    intro v
    rw [hb]
    simp [y]
  have hr : 1 - b ∈ sideIdeal D (fun v => !(side v)) := by
    rw [mem_sideIdeal]
    intro v
    rw [map_sub, map_one, hb]
    cases hs : side v <;> simp [y, hs]
  apply (Ideal.eq_top_iff_one _).mpr
  exact Submodule.mem_sup.mpr ⟨b, hl, 1 - b, hr, by abel⟩

theorem sideIdeal_mul_opposite (D : TateComparison.Data.SphericalPELAlbaneseData E K s q)
    (hgood : D.IsGoodCompletelySplitPrime)
    (hdegree : Module.finrank ℚ E = 2 * s) (side : Fin s → Bool) :
    sideIdeal D side * sideIdeal D (fun v => !(side v)) = qPowerIdeal E q 1 := by
  rw [Ideal.mul_eq_inf_of_coprime (sideIdeal_sup_opposite D hgood side),
    sideIdeal_inf_opposite D hgood hdegree]

theorem sideIdeal_ne_bot (D : TateComparison.Data.SphericalPELAlbaneseData E K s q) (side : Fin s → Bool) :
    sideIdeal D side ≠ ⊥ := by
  have hq : (q : 𝓞 E) ∈ sideIdeal D side := by
    rw [mem_sideIdeal]
    intro v
    change PadicInt.toZModPow 1 (D.localCharacter (v, side v) (q : 𝓞 E)) = 0
    rw [map_natCast, map_natCast]
    exact (congrArg (fun n : ℕ => (n : ZMod (q ^ 1))) (pow_one q).symm).trans
      (ZMod.natCast_self (q ^ 1))
  intro hz
  rw [hz, Ideal.mem_bot] at hq
  exact (Nat.cast_ne_zero.mpr (Fact.out : q.Prime).ne_zero) hq

theorem residueCoordinates_conjugate (D : TateComparison.Data.SphericalPELAlbaneseData E K s q)
    (hgood : D.IsGoodCompletelySplitPrime) (h : ℕ)
    (b : 𝓞 E) (v : Fin s) (w : Bool) :
    residueCoordinates D h (IsCMField.ringOfIntegersComplexConj E b) (v, w) =
      residueCoordinates D h b (v, !w) := by
  change PadicInt.toZModPow h (D.localCharacter (v, w)
    (IsCMField.ringOfIntegersComplexConj E b)) =
      PadicInt.toZModPow h (D.localCharacter (v, !w) b)
  rw [hgood.2.1 v w b]

theorem integral_conjugation_involutive (b : 𝓞 E) :
    IsCMField.ringOfIntegersComplexConj E (IsCMField.ringOfIntegersComplexConj E b) = b := by
  apply RingOfIntegers.ext
  change IsCMField.complexConj E (IsCMField.complexConj E (b : E)) = (b : E)
  exact IsCMField.complexConj_apply_apply E _

theorem sideIdeal_conjugate (D : TateComparison.Data.SphericalPELAlbaneseData E K s q)
    (hgood : D.IsGoodCompletelySplitPrime) (side : Fin s → Bool) :
    (sideIdeal D side).map (IsCMField.ringOfIntegersComplexConj E).toRingHom =
      sideIdeal D (fun v => !(side v)) := by
  ext b
  change b ∈ Ideal.map (IsCMField.ringOfIntegersComplexConj E).toRingEquiv
    (sideIdeal D side) ↔ _
  rw [Ideal.mem_map_of_equiv (IsCMField.ringOfIntegersComplexConj E).toRingEquiv]
  constructor
  · rintro ⟨a, ha, rfl⟩
    rw [mem_sideIdeal] at ha ⊢
    intro v
    change residueCoordinates D 1 (IsCMField.ringOfIntegersComplexConj E a)
      (v, !(side v)) = 0
    rw [residueCoordinates_conjugate D hgood]
    simpa using ha v
  · intro hb
    refine ⟨IsCMField.ringOfIntegersComplexConj E b, ?_, integral_conjugation_involutive b⟩
    rw [mem_sideIdeal] at hb ⊢
    intro v
    rw [residueCoordinates_conjugate D hgood]
    exact hb v

end

/-! Images of selected-side ideals in the actual q-adic coordinate rings.
They are (q) on a selected side and the whole ring on its opposite. -/

open _root_.NumberField

open OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Data

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]

theorem q_mem_sideIdeal (D : TateComparison.Data.SphericalPELAlbaneseData E K s q) (side : Fin s → Bool) :
    (q : 𝓞 E) ∈ sideIdeal D side := by
  rw [mem_sideIdeal]
  intro v
  change PadicInt.toZModPow 1 (D.localCharacter (v, side v) (q : 𝓞 E)) = 0
  rw [map_natCast, map_natCast]
  exact (congrArg (fun n : ℕ => (n : ZMod (q ^ 1))) (pow_one q).symm).trans
    (ZMod.natCast_self (q ^ 1))

theorem sideIdeal_map_selected (D : TateComparison.Data.SphericalPELAlbaneseData E K s q)
    (side : Fin s → Bool) (v : Fin s) :
    (sideIdeal D side).map (D.localCharacter (v, side v)) = Ideal.span {(q : ℤ_[q])} := by
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    intro b hb
    have hz := (mem_sideIdeal D side b).mp hb v
    have hm : D.localCharacter (v, side v) b ∈ RingHom.ker (PadicInt.toZModPow 1) := hz
    rw [PadicInt.ker_toZModPow, pow_one] at hm
    exact hm
  · apply Ideal.span_le.mpr
    intro z hz
    obtain rfl := Set.mem_singleton_iff.mp hz
    change (q : ℤ_[q]) ∈ (sideIdeal D side).map (D.localCharacter (v, side v))
    have hm := Ideal.mem_map_of_mem (D.localCharacter (v, side v)) (q_mem_sideIdeal D side)
    rw [map_natCast] at hm
    exact hm

theorem padic_unit_of_residue_one (z : ℤ_[q]) (hz : PadicInt.toZModPow 1 z = 1) : IsUnit z := by
  let : Fact (q ^ 1).Prime := ⟨by simpa only [pow_one] using (Fact.out : q.Prime)⟩
  by_contra hunit
  have hm : z ∈ IsLocalRing.maximalIdeal ℤ_[q] := by
    simpa only [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] using hunit
  rw [PadicInt.maximalIdeal_eq_span_p] at hm
  have hk : z ∈ RingHom.ker (PadicInt.toZModPow 1) := by
    rwa [PadicInt.ker_toZModPow, pow_one]
  have hzero : PadicInt.toZModPow 1 z = 0 := hk
  exact one_ne_zero (hz.symm.trans hzero)

theorem sideIdeal_map_unselected (D : TateComparison.Data.SphericalPELAlbaneseData E K s q)
    (hgood : D.IsGoodCompletelySplitPrime) (side : Fin s → Bool)
    (v : Fin s) (w : Bool) (hw : w ≠ side v) :
    (sideIdeal D side).map (D.localCharacter (v, w)) = ⊤ := by
  classical
  let y : Fin s × Bool → ZMod (q ^ 1) :=
    fun t => if t.2 = side t.1 then 0 else 1
  obtain ⟨b, hb⟩ := residueCoordinates_surjective D hgood 1 y
  have hmem : b ∈ sideIdeal D side := by
    rw [mem_sideIdeal]
    intro t
    rw [hb]
    simp [y]
  have hres : PadicInt.toZModPow 1 (D.localCharacter (v, w) b) = 1 := by
    change residueCoordinates D 1 b (v, w) = 1
    rw [hb]
    simp [y, hw]
  exact Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_map_of_mem _ hmem)
    (padic_unit_of_residue_one _ hres)

end

end OAI.AlgebraicGeometry.AbelianScheme.CentralAction.SideResidues.Construction
