import OAI.RepresentationTheory.Weil.AdelicSplitting.IntegralAdeles

/-! # Finite Lattices -/

namespace OAI.RepresentationTheory.Weil.AdelicSplitting.FiniteLattices.Construction

noncomputable section

section

/-! Every open finite-adelic additive subgroup contains a nonzero integer
multiple of the integral adeles. The exponent comes from a finite quotient
of the compact integral ring. -/

open scoped Classical _root_.NumberField

theorem compact_openAddSubgroup_integer_multiple
    {G : Type*} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] [CompactSpace G]
    (U : OpenAddSubgroup G) :
    ∃ M : ℕ, 0 < M ∧ ∀ x : G, M • x ∈ U := by
  let : Fintype (G ⧸ U.toAddSubgroup) := Fintype.ofFinite _
  refine ⟨Fintype.card (G ⧸ U.toAddSubgroup), Fintype.card_pos, fun x => ?_⟩
  have h := card_nsmul_eq_zero (x := QuotientAddGroup.mk' U.toAddSubgroup x)
  rw [← map_nsmul] at h
  exact (QuotientAddGroup.eq_zero_iff _).mp h

variable (F : Type) [Field F] [NumberField F]

theorem finite_openAddSubgroup_integer_multiple (U : OpenAddSubgroup (ArchimedeanAdeles.Construction.FiniteAdeles F)) :
    ∃ M : ℕ, 0 < M ∧ ∀ a : IntegralAdeles.Construction.finiteIntegralRing F,
      (M : ArchimedeanAdeles.Construction.FiniteAdeles F) * a.val ∈ U := by
  let V : OpenAddSubgroup (IntegralAdeles.Construction.finiteIntegralRing F) :=
    U.comap (IntegralAdeles.Construction.finiteIntegralRing F).toAddSubgroup.subtype continuous_subtype_val
  obtain ⟨M, hM, h⟩ := compact_openAddSubgroup_integer_multiple V
  refine ⟨M, hM, fun a => ?_⟩
  have ha := h a
  change (M • a).val ∈ U at ha
  simpa only [nsmul_eq_mul, Subring.coe_mul, Subring.coe_natCast] using ha

end

section

/-! Compactly supported locally constant finite-adelic test functions have
a uniform lattice of periods, given by a positive integer multiple of all
integral coordinate vectors. -/

open scoped Classical _root_.NumberField

section Stabilizer
variable {G : Type*} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]

def functionTranslationStabilizer (f : G → ℂ) : AddSubgroup G where
  carrier := {u | ∀ x, f (u + x) = f x}
  zero_mem' x := by rw [zero_add]
  add_mem' hu hv x := by rw [add_assoc, hu, hv]
  neg_mem' {u} hu x := by
    have h := hu (-u + x)
    rw [← add_assoc, add_neg_cancel, zero_add] at h
    exact h.symm

theorem functionTranslationStabilizer_isOpen (f : G → ℂ)
    (hlc : IsLocallyConstant f) (hs : HasCompactSupport f) :
    IsOpen (functionTranslationStabilizer f : Set G) := by
  let R : Set (G × G) := {p | f (p.1 + p.2) - f p.2 = 0}
  have hR : IsOpen R :=
    ((hlc.comp_continuous (continuous_fst.add continuous_snd)).sub
      (hlc.comp_continuous continuous_snd)).isOpen_fiber 0
  have hsub : ({0} : Set G) ×ˢ tsupport f ⊆ R := by
    rintro ⟨u, x⟩ ⟨rfl, _⟩
    simp [R]
  obtain ⟨U, W, hU, _, hU0, hKW, hUW⟩ := generalized_tube_lemma isCompact_singleton hs hR hsub
  have hsmall : U ∩ Neg.neg ⁻¹' U ⊆ (functionTranslationStabilizer f : Set G) := by
    rintro u ⟨hu, hnu⟩ x
    by_cases hx : x ∈ tsupport f
    · exact sub_eq_zero.mp (show f (u + x) - f x = 0 from hUW (show (u, x) ∈ U ×ˢ W from ⟨hu, hKW hx⟩))
    · by_cases hux : u + x ∈ tsupport f
      · have h : f (-u + (u + x)) = f (u + x) := sub_eq_zero.mp (hUW (show (-u, u + x) ∈ U ×ˢ W from ⟨hnu, hKW hux⟩))
        rw [← add_assoc, neg_add_cancel, zero_add] at h
        exact h.symm
      · rw [image_eq_zero_of_notMem_tsupport hux, image_eq_zero_of_notMem_tsupport hx]
  apply (functionTranslationStabilizer f).isOpen_of_mem_nhds (g := (0 : G))
  apply Filter.mem_of_superset ((hU.inter (hU.preimage continuous_neg)).mem_nhds ?_) hsmall
  exact ⟨hU0 rfl, by simpa only [Set.mem_preimage, neg_zero] using hU0 rfl⟩

end Stabilizer

variable (F : Type) [Field F] [NumberField F] {ι : Type*}

def integralPositionInclusion : (ι → IntegralAdeles.Construction.finiteIntegralRing F) →+ (ι → ArchimedeanAdeles.Construction.FiniteAdeles F) where
  toFun a i := (a i).val
  map_zero' := rfl
  map_add' _ _ := rfl

theorem integralPositionInclusion_continuous : Continuous (integralPositionInclusion F (ι := ι)) :=
  continuous_pi (fun i => continuous_subtype_val.comp (continuous_apply i))

theorem finitePosition_open_integer_multiple (U : OpenAddSubgroup (ι → ArchimedeanAdeles.Construction.FiniteAdeles F)) :
    ∃ M : ℕ, 0 < M ∧ ∀ a : ι → IntegralAdeles.Construction.finiteIntegralRing F, M • integralPositionInclusion F a ∈ U := by
  let V := U.comap (integralPositionInclusion F) (integralPositionInclusion_continuous F)
  obtain ⟨M, hM, h⟩ := compact_openAddSubgroup_integer_multiple V
  refine ⟨M, hM, fun a => ?_⟩
  have hh := h a
  change integralPositionInclusion F (M • a) ∈ U at hh
  rwa [map_nsmul] at hh

theorem finite_locallyConstant_integral_period (f : (ι → ArchimedeanAdeles.Construction.FiniteAdeles F) → ℂ)
    (hlc : IsLocallyConstant f) (hs : HasCompactSupport f) :
    ∃ M : ℕ, 0 < M ∧ ∀ (u : ι → IntegralAdeles.Construction.finiteIntegralRing F) (x : ι → ArchimedeanAdeles.Construction.FiniteAdeles F),
      f (M • integralPositionInclusion F u + x) = f x := by
  let U : OpenAddSubgroup (ι → ArchimedeanAdeles.Construction.FiniteAdeles F) :=
    ⟨functionTranslationStabilizer f, functionTranslationStabilizer_isOpen f hlc hs⟩
  obtain ⟨M, hM, h⟩ := finitePosition_open_integer_multiple F U
  exact ⟨M, hM, h⟩

end

/-! Compact open scalar lattices in the actual finite-adelic position space. -/

open scoped Classical _root_.NumberField

variable (F : Type) [Field F] [NumberField F] {ι : Type*}

def finiteIntegralPositions : Subring (ι → ArchimedeanAdeles.Construction.FiniteAdeles F) where
  carrier := {x | ∀ i, x i ∈ IntegralAdeles.Construction.finiteIntegralRing F}
  zero_mem' := fun _ => zero_mem _
  one_mem' := fun _ => one_mem _
  add_mem' hx hy i := (IntegralAdeles.Construction.finiteIntegralRing F).add_mem (hx i) (hy i)
  mul_mem' hx hy i := (IntegralAdeles.Construction.finiteIntegralRing F).mul_mem (hx i) (hy i)
  neg_mem' hx i := (IntegralAdeles.Construction.finiteIntegralRing F).neg_mem (hx i)

theorem finiteIntegralPositions_isCompact :
    IsCompact (finiteIntegralPositions F (ι := ι) : Set (ι → ArchimedeanAdeles.Construction.FiniteAdeles F)) :=
  isCompact_pi_infinite (fun _ => IntegralAdeles.Construction.isCompact_finiteIntegralRing F)

theorem finiteIntegralPositions_isOpen [Fintype ι] :
    IsOpen (finiteIntegralPositions F (ι := ι) : Set (ι → ArchimedeanAdeles.Construction.FiniteAdeles F)) := by
  change IsOpen {x : ι → ArchimedeanAdeles.Construction.FiniteAdeles F | ∀ i, x i ∈ IntegralAdeles.Construction.finiteIntegralRing F}
  convert isOpen_iInter_of_finite
    (fun i : ι => (IntegralAdeles.Construction.isOpen_finiteIntegralRing F).preimage (continuous_apply i)) using 1
  ext x
  simp

variable {F}

def finitePositionScale (q : F) (x : ι → ArchimedeanAdeles.Construction.FiniteAdeles F) : ι → ArchimedeanAdeles.Construction.FiniteAdeles F :=
  fun i => algebraMap F (ArchimedeanAdeles.Construction.FiniteAdeles F) q * x i

theorem finitePositionScale_mul (p q : F) (x : ι → ArchimedeanAdeles.Construction.FiniteAdeles F) :
    finitePositionScale p (finitePositionScale q x) = finitePositionScale (p * q) x := by
  ext i
  simp only [finitePositionScale, map_mul, mul_assoc]

theorem finitePositionScale_one (x : ι → ArchimedeanAdeles.Construction.FiniteAdeles F) : finitePositionScale 1 x = x := by
  ext i
  simp [finitePositionScale]

def finitePositionScaleEquiv (q : F) (hq : q ≠ 0) : (ι → ArchimedeanAdeles.Construction.FiniteAdeles F) ≃+ (ι → ArchimedeanAdeles.Construction.FiniteAdeles F) where
  toFun := finitePositionScale q
  invFun := finitePositionScale q⁻¹
  left_inv x := by rw [finitePositionScale_mul, inv_mul_cancel₀ hq, finitePositionScale_one]
  right_inv x := by rw [finitePositionScale_mul, mul_inv_cancel₀ hq, finitePositionScale_one]
  map_add' x y := by ext i; simp [finitePositionScale, mul_add]

theorem finitePositionScale_continuous (q : F) : Continuous (finitePositionScale (ι := ι) q) :=
  continuous_pi (fun i => continuous_const.mul (continuous_apply i))

def finitePositionScaleHomeomorph (q : F) (hq : q ≠ 0) : (ι → ArchimedeanAdeles.Construction.FiniteAdeles F) ≃ₜ (ι → ArchimedeanAdeles.Construction.FiniteAdeles F) where
  toEquiv := (finitePositionScaleEquiv q hq).toEquiv
  continuous_toFun := finitePositionScale_continuous q
  continuous_invFun := finitePositionScale_continuous q⁻¹

def finiteAdelicPositionLattice (q : F) (hq : q ≠ 0) : AddSubgroup (ι → ArchimedeanAdeles.Construction.FiniteAdeles F) :=
  (finiteIntegralPositions F).toAddSubgroup.map (finitePositionScaleEquiv q hq).toAddMonoidHom

theorem finiteAdelicPositionLattice_mem_iff (q : F) (hq : q ≠ 0) (x : ι → ArchimedeanAdeles.Construction.FiniteAdeles F) :
    x ∈ finiteAdelicPositionLattice q hq ↔ finitePositionScale q⁻¹ x ∈ finiteIntegralPositions F := by
  constructor
  · rintro ⟨u, hu, rfl⟩
    change finitePositionScale q⁻¹ (finitePositionScale q u) ∈ finiteIntegralPositions F
    rw [finitePositionScale_mul, inv_mul_cancel₀ hq, finitePositionScale_one]
    exact hu
  · intro hx
    exact ⟨finitePositionScale q⁻¹ x, hx, (finitePositionScaleEquiv q hq).apply_symm_apply x⟩

theorem finiteAdelicPositionLattice_isCompact (q : F) (hq : q ≠ 0) :
    IsCompact (finiteAdelicPositionLattice (ι := ι) q hq : Set (ι → ArchimedeanAdeles.Construction.FiniteAdeles F)) :=
  (finiteIntegralPositions_isCompact F).image (finitePositionScale_continuous q)

theorem finiteAdelicPositionLattice_isOpen [Fintype ι] (q : F) (hq : q ≠ 0) :
    IsOpen (finiteAdelicPositionLattice (ι := ι) q hq : Set (ι → ArchimedeanAdeles.Construction.FiniteAdeles F)) :=
  (finitePositionScaleHomeomorph q hq).isOpenMap _ (finiteIntegralPositions_isOpen F)

theorem finitePositionScale_natCast (M : ℕ) (x : ι → ArchimedeanAdeles.Construction.FiniteAdeles F) :
    finitePositionScale (M : F) x = M • x := by
  ext i
  simp [finitePositionScale, nsmul_eq_mul]

theorem finite_locallyConstant_lattice_period
    (f : (ι → ArchimedeanAdeles.Construction.FiniteAdeles F) → ℂ) (hlc : IsLocallyConstant f) (hs : HasCompactSupport f) :
    ∃ M : ℕ, ∃ hM : 0 < M,
      ∀ u ∈ finiteAdelicPositionLattice (M : F) (by exact_mod_cast hM.ne'), ∀ x, f (u + x) = f x := by
  obtain ⟨M, hM, h⟩ := finite_locallyConstant_integral_period F f hlc hs
  refine ⟨M, hM, ?_⟩
  rintro u ⟨v, hv, rfl⟩ x
  change f (finitePositionScale (M : F) v + x) = f x
  rw [finitePositionScale_natCast]
  exact h (fun i => ⟨v i, hv i⟩) x

theorem rational_mem_finiteAdelicPositionLattice_iff (q : F) (hq : q ≠ 0) (x : ι → F) :
    (fun i => algebraMap F (ArchimedeanAdeles.Construction.FiniteAdeles F) (x i)) ∈ finiteAdelicPositionLattice q hq ↔
      ∀ i, ∃ r : 𝓞 F, q * algebraMap (𝓞 F) F r = x i := by
  rw [finiteAdelicPositionLattice_mem_iff]
  change (∀ i, algebraMap F (ArchimedeanAdeles.Construction.FiniteAdeles F) q⁻¹ * algebraMap F (ArchimedeanAdeles.Construction.FiniteAdeles F) (x i) ∈
    IntegralAdeles.Construction.finiteIntegralRing F) ↔ _
  simp only [← map_mul, IntegralAdeles.Construction.rational_mem_finiteIntegral_iff]
  apply forall_congr'
  intro i
  apply exists_congr
  intro r
  constructor
  · intro hr
    rw [hr, ← mul_assoc, mul_inv_cancel₀ hq, one_mul]
  · intro hr
    rw [← hr, ← mul_assoc, inv_mul_cancel₀ hq, one_mul]

end

end OAI.RepresentationTheory.Weil.AdelicSplitting.FiniteLattices.Construction
