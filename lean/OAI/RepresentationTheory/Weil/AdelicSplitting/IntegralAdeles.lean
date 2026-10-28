import OAI.RepresentationTheory.Weil.AdelicSplitting.LocalCompact

/-! # Integral Adeles -/

namespace OAI.RepresentationTheory.Weil.AdelicSplitting.IntegralAdeles.Construction

noncomputable section

/-! The compact open ring of integral finite adeles, and clearing one
common denominator on compact subsets over any number field. -/

open scoped _root_.NumberField Classical RestrictedProduct
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

variable (F : Type) [Field F] [NumberField F]

def finiteIntegralRing : Subring (ArchimedeanAdeles.Construction.FiniteAdeles F) where
  carrier := {a | ∀ v : HeightOneSpectrum (𝓞 F), a v ∈ v.adicCompletionIntegers F}
  zero_mem' v := (v.adicCompletionIntegers F).zero_mem
  one_mem' v := (v.adicCompletionIntegers F).one_mem
  add_mem' ha hb v := (v.adicCompletionIntegers F).toSubring.add_mem (ha v) (hb v)
  mul_mem' ha hb v := (v.adicCompletionIntegers F).toSubring.mul_mem (ha v) (hb v)
  neg_mem' ha v := (v.adicCompletionIntegers F).toSubring.neg_mem (ha v)

theorem isOpen_finiteIntegralRing : IsOpen (finiteIntegralRing F : Set (ArchimedeanAdeles.Construction.FiniteAdeles F)) :=
  RestrictedProduct.isOpen_forall_mem
    (fun v : HeightOneSpectrum (𝓞 F) => Valued.isOpen_valuationSubring (v.adicCompletion F))

def finiteIntegralProductHomeomorph :
    (∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletionIntegers F) ≃ₜ finiteIntegralRing F :=
  (RestrictedProduct.isEmbedding_structureMap
    (R := fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
    (A := fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F)))
    (𝓕 := Filter.cofinite)).toHomeomorph.trans
      (Homeomorph.setCongr (by rw [RestrictedProduct.range_structureMap]; rfl))

instance e26FiniteIntegerCompact (v : HeightOneSpectrum (𝓞 F)) :
    CompactSpace (v.adicCompletionIntegers F) := by
  apply isCompact_iff_compactSpace.mp
  have he : (v.adicCompletionIntegers F : Set (v.adicCompletion F)) =
      Metric.closedBall (0 : v.adicCompletion F) 1 := by
    ext x
    simp only [Metric.mem_closedBall, dist_zero_right, Valued.toNormedField.norm_le_one_iff]
    rfl
  rw [he]
  exact isCompact_closedBall _ _

instance e26FiniteIntegralCompact : CompactSpace (finiteIntegralRing F) :=
  (finiteIntegralProductHomeomorph F).compactSpace

theorem isCompact_finiteIntegralRing : IsCompact (finiteIntegralRing F : Set (ArchimedeanAdeles.Construction.FiniteAdeles F)) :=
  isCompact_iff_compactSpace.mpr (inferInstanceAs (CompactSpace (finiteIntegralRing F)))

theorem algebraMap_mem_finiteIntegralRing (a : 𝓞 F) :
    algebraMap (𝓞 F) (ArchimedeanAdeles.Construction.FiniteAdeles F) a ∈ finiteIntegralRing F := by
  intro v
  exact coe_mem_adicCompletionIntegers (K := F) v a

def integerToFiniteIntegral : 𝓞 F →+* finiteIntegralRing F :=
  (algebraMap (𝓞 F) (ArchimedeanAdeles.Construction.FiniteAdeles F)).codRestrict (finiteIntegralRing F)
    (algebraMap_mem_finiteIntegralRing F)

theorem integerToFiniteIntegral_eq_product (a : 𝓞 F) :
    integerToFiniteIntegral F a = finiteIntegralProductHomeomorph F
      (fun v => algebraMap (𝓞 F) (v.adicCompletionIntegers F) a) := rfl

theorem exists_integer_multiple_finiteIntegral (a : ArchimedeanAdeles.Construction.FiniteAdeles F) :
    ∃ r : 𝓞 F, r ≠ 0 ∧ algebraMap (𝓞 F) (ArchimedeanAdeles.Construction.FiniteAdeles F) r * a ∈ finiteIntegralRing F := by
  have hs : {v : HeightOneSpectrum (𝓞 F) | a v ∉ v.adicCompletionIntegers F}.Finite :=
    Filter.eventually_cofinite.mp a.property
  choose d hd hda using (fun v : HeightOneSpectrum (𝓞 F) =>
    adicCompletion.mul_nonZeroDivisor_mem_adicCompletionIntegers v (a v))
  let r : 𝓞 F := ∏ v ∈ hs.toFinset, d v
  refine ⟨r, Finset.prod_ne_zero_iff.mpr (fun v _ => nonZeroDivisors.ne_zero (hd v)), ?_⟩
  intro v
  change algebraMap (𝓞 F) (v.adicCompletion F) r * a v ∈ v.adicCompletionIntegers F
  by_cases hv : v ∈ hs.toFinset
  · obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem d hv
    change r = d v * k at hk
    rw [hk, map_mul]
    have h := (v.adicCompletionIntegers F).mul_mem _ _ (hda v)
      (coe_mem_adicCompletionIntegers (K := F) v k)
    simpa only [Algebra.cast, mul_assoc, mul_left_comm, mul_comm] using! h
  · have ha : a v ∈ v.adicCompletionIntegers F := by simpa using hv
    exact (v.adicCompletionIntegers F).mul_mem _ _
      (coe_mem_adicCompletionIntegers (K := F) v r) ha

theorem rational_mem_finiteIntegral_iff (q : F) :
    algebraMap F (ArchimedeanAdeles.Construction.FiniteAdeles F) q ∈ finiteIntegralRing F ↔
      ∃ r : 𝓞 F, algebraMap (𝓞 F) F r = q := by
  constructor
  · intro h
    apply mem_integers_of_valuation_le_one (R := 𝓞 F) (K := F) q
    intro v
    simpa only [mem_adicCompletionIntegers, FiniteAdeleRing.algebraMap_apply,
      valuedAdicCompletion_eq_valuation'] using h v
  · rintro ⟨r, rfl⟩
    rw [← IsScalarTower.algebraMap_apply]
    exact algebraMap_mem_finiteIntegralRing F r

variable {ι : Type*} [Fintype ι]

def finiteIntegralBox (r : 𝓞 F) : Set (ι → ArchimedeanAdeles.Construction.FiniteAdeles F) :=
  {a | ∀ i, algebraMap (𝓞 F) (ArchimedeanAdeles.Construction.FiniteAdeles F) r * a i ∈ finiteIntegralRing F}

theorem isOpen_finiteIntegralBox (r : 𝓞 F) :
    IsOpen (finiteIntegralBox F (ι := ι) r) := by
  simp only [finiteIntegralBox, Set.ofPred_forall]
  apply isOpen_iInter_of_finite
  intro i
  exact (isOpen_finiteIntegralRing F).preimage (continuous_const.mul (continuous_apply i))

omit [Fintype ι] in
theorem finiteIntegralBox_mono {r s : 𝓞 F} (h : r ∣ s) :
    finiteIntegralBox F (ι := ι) r ⊆ finiteIntegralBox F s := by
  obtain ⟨t, rfl⟩ := h
  intro a ha i
  have hh := (finiteIntegralRing F).mul_mem (algebraMap_mem_finiteIntegralRing F t) (ha i)
  simpa only [map_mul, mul_assoc, mul_left_comm] using hh

theorem exists_finiteIntegralBox (a : ι → ArchimedeanAdeles.Construction.FiniteAdeles F) :
    ∃ r : 𝓞 F, r ≠ 0 ∧ a ∈ finiteIntegralBox F r := by
  choose r hr ha using fun i => exists_integer_multiple_finiteIntegral F (a i)
  refine ⟨∏ i, r i, Finset.prod_ne_zero_iff.mpr (fun i _ => hr i), ?_⟩
  intro i
  have hd := Finset.dvd_prod_of_mem r (Finset.mem_univ i)
  obtain ⟨t, ht⟩ := hd
  rw [ht, map_mul, mul_right_comm]
  exact (finiteIntegralRing F).mul_mem (ha i) (algebraMap_mem_finiteIntegralRing F t)

theorem compact_subset_finiteIntegralBox (K : Set (ι → ArchimedeanAdeles.Construction.FiniteAdeles F)) (hK : IsCompact K) :
    ∃ r : 𝓞 F, r ≠ 0 ∧ K ⊆ finiteIntegralBox F r := by
  let U := fun r : {r : 𝓞 F // r ≠ 0} => finiteIntegralBox F (ι := ι) r.val
  let : Nonempty {r : 𝓞 F // r ≠ 0} := ⟨⟨1, one_ne_zero⟩⟩
  have hcover : K ⊆ ⋃ r, U r := by
    intro a _
    obtain ⟨r, hr, ha⟩ := exists_finiteIntegralBox F a
    exact Set.mem_iUnion.mpr ⟨⟨r, hr⟩, ha⟩
  have hdir : Directed (· ⊆ ·) U := by
    intro r s
    exact ⟨⟨r.val * s.val, mul_ne_zero r.property s.property⟩,
      finiteIntegralBox_mono F (dvd_mul_right _ _), finiteIntegralBox_mono F (dvd_mul_left _ _)⟩
  obtain ⟨r, hr⟩ := hK.elim_directed_cover U (fun r => isOpen_finiteIntegralBox F r.val) hcover hdir
  exact ⟨r.val, r.property, hr⟩

end

end OAI.RepresentationTheory.Weil.AdelicSplitting.IntegralAdeles.Construction
