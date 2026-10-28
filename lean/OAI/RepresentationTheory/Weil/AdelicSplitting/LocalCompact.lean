import OAI.RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles

/-! # Local Compact -/

namespace OAI.RepresentationTheory.Weil.AdelicSplitting.LocalCompact.Construction

noncomputable section

section

/-! Local compactness of the actual finite completions. The proof uses
density, integral approximation, and finiteness of the residue field. -/

open scoped _root_.NumberField
open IsDedekindDomain

variable (F : Type*) [Field F] [NumberField F]
  (v : HeightOneSpectrum (𝓞 F))

theorem integral_approximation (x : v.adicCompletionIntegers F) :
    ∃ a : 𝓞 F, ‖algebraMap (𝓞 F) (v.adicCompletion F) a - x.val‖ < 1 := by
  obtain ⟨q, hq⟩ := (HeightOneSpectrum.denseRange_algebraMap (K := F) v).exists_dist_lt
    x.val (by norm_num : (0 : ℝ) < 1)
  rw [dist_eq_norm] at hq
  rw [norm_sub_rev] at hq
  have hx : ‖x.val‖ ≤ 1 := (Valued.toNormedField.norm_le_one_iff).mpr x.property
  have hqint : ‖algebraMap F (v.adicCompletion F) q‖ ≤ 1 := by
    calc
      ‖algebraMap F (v.adicCompletion F) q‖ =
          ‖(algebraMap F (v.adicCompletion F) q - x.val) + x.val‖ := by rw [sub_add_cancel]
      _ ≤ max ‖algebraMap F (v.adicCompletion F) q - x.val‖ ‖x.val‖ := Valuation.norm_add_le Valued.v _ _
      _ ≤ 1 := max_le hq.le hx
  have hqval : v.valuation F q ≤ 1 := by
    have h := (Valued.toNormedField.norm_le_one_iff).mp hqint
    change Valued.v (q : v.adicCompletion F) ≤ 1 at h
    rwa [HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] at h
  obtain ⟨a, ha⟩ := HeightOneSpectrum.exists_valuation_sub_lt_of_integer v hqval 1
  refine ⟨a, ?_⟩
  have haq : ‖algebraMap (𝓞 F) (v.adicCompletion F) a -
      algebraMap F (v.adicCompletion F) q‖ < 1 := by
    apply (Valued.toNormedField.norm_lt_one_iff).mpr
    rw [IsScalarTower.algebraMap_apply (𝓞 F) F (v.adicCompletion F), ← map_sub]
    change Valued.v ((algebraMap (𝓞 F) F a - q : F) : v.adicCompletion F) < 1
    rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    exact ha
  calc
    ‖algebraMap (𝓞 F) (v.adicCompletion F) a - x.val‖ =
        ‖(algebraMap (𝓞 F) (v.adicCompletion F) a - algebraMap F (v.adicCompletion F) q) +
          (algebraMap F (v.adicCompletion F) q - x.val)‖ := by rw [sub_add_sub_cancel]
    _ ≤ max ‖algebraMap (𝓞 F) (v.adicCompletion F) a - algebraMap F (v.adicCompletion F) q‖
          ‖algebraMap F (v.adicCompletion F) q - x.val‖ := Valuation.norm_add_le Valued.v _ _
    _ < 1 := max_lt haq hq

def integralResidueMap : 𝓞 F →+* IsLocalRing.ResidueField (v.adicCompletionIntegers F) :=
  (IsLocalRing.residue _).comp (algebraMap (𝓞 F) (v.adicCompletionIntegers F))

theorem integralResidueMap_surjective : Function.Surjective (integralResidueMap F v) := by
  intro y
  obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective y
  obtain ⟨a, ha⟩ := integral_approximation F v x
  refine ⟨a, ?_⟩
  change IsLocalRing.residue _ (algebraMap (𝓞 F) (v.adicCompletionIntegers F) a) =
    IsLocalRing.residue _ x
  rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]
  apply (Valuation.mem_maximalIdeal_iff
    (v := (Valued.v : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ))))).mpr
  exact (Valued.toNormedField.norm_lt_one_iff).mp ha

theorem prime_le_residueKernel : v.asIdeal ≤ RingHom.ker (integralResidueMap F v) := by
  intro a ha
  change IsLocalRing.residue _ (algebraMap (𝓞 F) (v.adicCompletionIntegers F) a) = 0
  rw [IsLocalRing.residue_eq_zero_iff]
  apply (Valuation.mem_maximalIdeal_iff
    (v := (Valued.v : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ))))).mpr
  change Valued.v ((algebraMap (𝓞 F) F a : F) : v.adicCompletion F) < 1
  rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation',
    HeightOneSpectrum.valuation_of_algebraMap]
  exact (HeightOneSpectrum.intValuation_lt_one_iff_mem v a).mpr ha

instance finiteCompletionResidueField : Finite (IsLocalRing.ResidueField (v.adicCompletionIntegers F)) := by
  let r := integralResidueMap F v
  have hk : RingHom.ker r ≠ ⊥ := fun h => v.ne_bot (le_bot_iff.mp (h ▸ prime_le_residueKernel F v))
  let : Finite ((𝓞 F) ⧸ RingHom.ker r) := (RingHom.ker r).finiteQuotientOfFreeOfNeBot hk
  exact Finite.of_surjective (r.quotientKerEquivOfSurjective (integralResidueMap_surjective F v))
    (r.quotientKerEquivOfSurjective (integralResidueMap_surjective F v)).surjective

instance finiteCompletionProperSpace : ProperSpace (v.adicCompletion F) := by
  apply (Valued.integer.properSpace_iff_completeSpace_and_isDiscreteValuationRing_integer_and_finite_residueField).mpr
  exact ⟨inferInstance, inferInstanceAs (IsDiscreteValuationRing (v.adicCompletionIntegers F)),
    finiteCompletionResidueField F v⟩

instance completionLocallyCompactSpace (w : ArchimedeanAdeles.Construction.Places F) :
    LocallyCompactSpace (ArchimedeanAdeles.Construction.Completion F w) := by
  cases w <;> infer_instance

end

/-! One algebraic-integer denominator clears every point of a compact set
in a finite completion, in all position coordinates at once. -/

open scoped Classical _root_.NumberField
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

variable (F : Type) [Field F] [NumberField F]
  (v : HeightOneSpectrum (𝓞 F)) (N : ℕ)

def localIntegerPositionBox (r : 𝓞 F) : Set (Fin N → v.adicCompletion F) :=
  {x | ∀ i, algebraMap (𝓞 F) (v.adicCompletion F) r * x i ∈ v.adicCompletionIntegers F}

theorem isOpen_localIntegerPositionBox (r : 𝓞 F) : IsOpen (localIntegerPositionBox F v N r) := by
  simp only [localIntegerPositionBox, Set.ofPred_forall]
  apply isOpen_iInter_of_finite
  intro i
  exact (Valued.isOpen_valuationSubring (v.adicCompletion F)).preimage
    (continuous_const.mul (continuous_apply i))

theorem localIntegerPositionBox_mono {r s : 𝓞 F} (h : r ∣ s) :
    localIntegerPositionBox F v N r ⊆ localIntegerPositionBox F v N s := by
  obtain ⟨t, rfl⟩ := h
  intro x hx i
  have hh := (v.adicCompletionIntegers F).toSubring.mul_mem
    (coe_mem_adicCompletionIntegers (K := F) v t) (hx i)
  simpa only [map_mul, mul_assoc, mul_left_comm] using! hh

theorem exists_localIntegerPositionBox (x : Fin N → v.adicCompletion F) :
    ∃ r : 𝓞 F, r ≠ 0 ∧ x ∈ localIntegerPositionBox F v N r := by
  choose r hr hx using fun i => adicCompletion.mul_nonZeroDivisor_mem_adicCompletionIntegers v (x i)
  let R : 𝓞 F := ∏ i, r i
  refine ⟨R, Finset.prod_ne_zero_iff.mpr (fun i _ => nonZeroDivisors.ne_zero (hr i)), fun i => ?_⟩
  obtain ⟨t, ht⟩ := Finset.dvd_prod_of_mem r (Finset.mem_univ i)
  change R = r i * t at ht
  rw [ht, map_mul]
  have hh := (v.adicCompletionIntegers F).toSubring.mul_mem (hx i)
    (coe_mem_adicCompletionIntegers (K := F) v t)
  simpa only [Algebra.cast, mul_assoc, mul_comm, mul_left_comm] using! hh

theorem compact_local_integer_denominator (K : Set (Fin N → v.adicCompletion F)) (hK : IsCompact K) :
    ∃ r : 𝓞 F, r ≠ 0 ∧ K ⊆ localIntegerPositionBox F v N r := by
  let U := fun r : {r : 𝓞 F // r ≠ 0} => localIntegerPositionBox F v N r.val
  let : Nonempty {r : 𝓞 F // r ≠ 0} := ⟨⟨1, one_ne_zero⟩⟩
  have hcover : K ⊆ ⋃ r, U r := by
    intro x _
    obtain ⟨r, hr, hx⟩ := exists_localIntegerPositionBox F v N x
    exact Set.mem_iUnion.mpr ⟨⟨r, hr⟩, hx⟩
  have hdir : Directed (· ⊆ ·) U := by
    intro r s
    exact ⟨⟨r.val * s.val, mul_ne_zero r.property s.property⟩,
      localIntegerPositionBox_mono F v N (dvd_mul_right _ _),
      localIntegerPositionBox_mono F v N (dvd_mul_left _ _)⟩
  obtain ⟨r, hr⟩ := hK.elim_directed_cover U
    (fun r => isOpen_localIntegerPositionBox F v N r.val) hcover hdir
  exact ⟨r.val, r.property, hr⟩

end

end OAI.RepresentationTheory.Weil.AdelicSplitting.LocalCompact.Construction
