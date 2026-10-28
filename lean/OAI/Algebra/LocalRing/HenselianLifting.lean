import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Idempotents
import Mathlib.RingTheory.Etale.Finite
import Mathlib.RingTheory.Unramified.LocalStructure
import Mathlib.RingTheory.Polynomial.UniversalFactorizationRing
import Mathlib.RingTheory.IntegralClosure.Algebra.Ideal
import Mathlib.RingTheory.Unramified.Finite
import Mathlib.Algebra.Polynomial.Lifts

/-! # Henselian Lifting -/

namespace OAI.Algebra.LocalRing.HenselianLifting.Construction

/-!
# HenselianLifting: henselian lifting of idempotents and finite étale algebras

This file proves both declarations specified in `Statements/HenselianLifting.lean`, using
only Mathlib imports. Hensel's lemma first lifts points of standard étale
algebras and then coprime polynomial factorizations. Applying this to a monic
annihilator of `b * (b - 1)` gives idempotent lifting in every finite algebra.

For morphisms, a separability idempotent describes a residue-field section;
lifting that idempotent and applying Nakayama produces a unique section.
Finite separable field extensions lift by lifting monic separable polynomials,
and finite products give all finite étale residue-field algebras.
-/

open _root_.CategoryTheory _root_.Polynomial IsLocalRing
open scoped TensorProduct

universe u v

theorem standardEtale_lift
    (R : Type u) [CommRing R] [HenselianLocalRing R]
    (P : StandardEtalePair R)
    (φ : P.Ring →ₐ[R] ResidueField R) :
    ∃ ψ : P.Ring →ₐ[R] R,
      (Algebra.ofId R (ResidueField R)).comp ψ = φ := by
  have hx := P.hasMap_X.map φ
  obtain ⟨a, ha, ha₀⟩ :=
    ((HenselianLocalRing.TFAE R).out 1 2 rfl rfl).mp inferInstance
      P.f P.monic_f (φ P.X) hx.1 hx.isUnit_derivative_f.ne_zero
  have hg : IsUnit (aeval a P.g) := by
    apply (residue_ne_zero_iff_isUnit _).mp
    have hmap : residue R (aeval a P.g) = aeval (φ P.X) P.g := by
      rw [← ha₀]
      exact (Polynomial.aeval_algHom_apply (Algebra.ofId R (ResidueField R)) a P.g).symm
    rw [hmap]
    exact hx.2.ne_zero
  have haf : aeval a P.f = 0 := ha
  have hPa : P.HasMap a := ⟨haf, hg⟩
  let ψ := P.lift a hPa
  refine ⟨ψ, P.hom_ext ?_⟩
  exact (congrArg (residue R) (P.lift_X a hPa)).trans ha₀

theorem etale_lift_to_henselian
    (R : Type u) [CommRing R] [HenselianLocalRing R]
    (S : Type v) [CommRing S] [Algebra R S] [Algebra.Etale R S]
    (φ : S →ₐ[R] ResidueField R) :
    ∃ ψ : S →ₐ[R] R,
      (Algebra.ofId R (ResidueField R)).comp ψ = φ := by
  let Q := RingHom.ker φ.toRingHom
  have : Q.IsPrime := RingHom.ker_isPrime φ.toRingHom
  obtain ⟨s, hs, hstd⟩ := Algebra.IsEtaleAt.exists_isStandardEtale (R := R) Q
  let := hstd
  let φ' : Localization.Away s →ₐ[R] ResidueField R :=
    IsLocalization.Away.liftAlgHom s (isUnit_iff_ne_zero.mpr hs)
  let P : StandardEtalePresentation R (Localization.Away s) :=
    Classical.choice Algebra.IsStandardEtale.nonempty_standardEtalePresentation
  obtain ⟨ψ, hψ⟩ := standardEtale_lift R P.P
    (φ'.comp P.equivRing.symm.toAlgHom)
  refine ⟨(ψ.comp P.equivRing.toAlgHom).comp
    (IsScalarTower.toAlgHom R S (Localization.Away s)), ?_⟩
  ext x
  have h := AlgHom.congr_fun hψ (P.equivRing (algebraMap S (Localization.Away s) x))
  simpa [φ'] using h

theorem lift_coprime_factors
    (R : Type u) [CommRing R] [HenselianLocalRing R]
    (n m k : ℕ) (hn : n = m + k) (p : MonicDegreeEq R n)
    (q : MonicDegreeEq (ResidueField R) m)
    (r : MonicDegreeEq (ResidueField R) k)
    (hfac : q.1 * r.1 = p.1.map (residue R))
    (hcop : IsCoprime q.1 r.1) :
    ∃ (q' : MonicDegreeEq R m) (r' : MonicDegreeEq R k),
      q'.1 * r'.1 = p.1 ∧ IsCoprime q'.1 r'.1 ∧
      q'.map (residue R) = q ∧ r'.map (residue R) = r := by
  let E := UniversalCoprimeFactorizationRing m k hn p
  have hfac' : q.1 * r.1 = p.1.map (algebraMap R (ResidueField R)) := hfac
  let z₀ : { z : MonicDegreeEq (ResidueField R) m × MonicDegreeEq (ResidueField R) k //
      z.1.1 * z.2.1 = p.1.map (algebraMap R (ResidueField R)) ∧
      IsCoprime z.1.1 z.2.1 } := ⟨(q, r), hfac', hcop⟩
  let φ : E →ₐ[R] ResidueField R :=
    (UniversalCoprimeFactorizationRing.homEquiv (ResidueField R) m k hn p).symm
      z₀
  obtain ⟨ψ, hψ⟩ := etale_lift_to_henselian R E φ
  let z := UniversalCoprimeFactorizationRing.homEquiv R m k hn p ψ
  refine ⟨z.1.1, z.1.2, ?_, z.2.2, ?_, ?_⟩
  · simpa using z.2.1
  · have h := UniversalCoprimeFactorizationRing.homEquiv_comp_fst R m k hn p ψ
      (Algebra.ofId R (ResidueField R))
    rw [hψ] at h
    exact h.symm.trans (congrArg (fun z => z.1.1)
      ((UniversalCoprimeFactorizationRing.homEquiv (ResidueField R) m k hn p).apply_symm_apply z₀))
  · have h := UniversalCoprimeFactorizationRing.homEquiv_comp_snd R m k hn p ψ
      (Algebra.ofId R (ResidueField R))
    rw [hψ] at h
    exact h.symm.trans (congrArg (fun z => z.1.2)
      ((UniversalCoprimeFactorizationRing.homEquiv (ResidueField R) m k hn p).apply_symm_apply z₀))

theorem lift_coprime_factorization
    (R : Type u) [CommRing R] [HenselianLocalRing R]
    (p : R[X]) (hp : p.Monic)
    (q r : (ResidueField R)[X]) (hq : q.Monic) (hr : r.Monic)
    (hfac : p.map (residue R) = q * r) (hcop : IsCoprime q r) :
    ∃ q' r' : R[X], q'.Monic ∧ r'.Monic ∧ p = q' * r' ∧
      IsCoprime q' r' ∧ q'.map (residue R) = q ∧ r'.map (residue R) = r := by
  have hn : p.natDegree = q.natDegree + r.natDegree := by
    simpa [hp.natDegree_map, hq.natDegree_mul hr] using congrArg natDegree hfac
  obtain ⟨q', r', hprod, hcop', hq', hr'⟩ := lift_coprime_factors R _ _ _ hn
    (.mk p hp rfl) (.mk q hq rfl) (.mk r hr rfl) hfac.symm hcop
  exact ⟨q'.1, r'.1, q'.monic, r'.monic, hprod.symm, hcop',
    congrArg Subtype.val hq', congrArg Subtype.val hr'⟩

theorem exists_idempotent_lift
    (R : Type u) [CommRing R] [HenselianLocalRing R]
    (B : Type v) [CommRing B] [Algebra R B] [Module.Finite R B]
    (e₀ : B ⧸ (maximalIdeal R).map (algebraMap R B))
    (he₀ : IsIdempotentElem e₀) :
    ∃ e : B, IsIdempotentElem e ∧
      Ideal.Quotient.mk ((maximalIdeal R).map (algebraMap R B)) e = e₀ := by
  nontriviality B
  let I := (maximalIdeal R).map (algebraMap R B)
  let π := Ideal.Quotient.mkₐ R I
  let : Algebra (ResidueField R) (B ⧸ I) :=
    Ideal.Quotient.algebraQuotientOfLEComap Ideal.le_comap_map
  have : IsScalarTower R (ResidueField R) (B ⧸ I) :=
    IsScalarTower.of_algebraMap_eq' rfl
  obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective e₀
  have hbI : b * (b - 1) ∈ I := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    simp only [I, map_mul, map_sub, hb, mul_sub, mul_one, he₀.eq, sub_self]
  obtain ⟨f, hf, hfb, hcoeff⟩ :=
    Polynomial.exists_monic_aeval_eq_zero_forall_mem_of_mem_map hbI
  have hn : f.natDegree ≠ 0 := by
    intro h
    have hf1 := eq_one_of_monic_natDegree_zero hf h
    simp [hf1] at hfb
  have hfbar : f.map (residue R) = X ^ f.natDegree := by
    ext i
    by_cases hi : i = f.natDegree
    · subst i
      simp [hf.coeff_natDegree]
    · have hc : residue R (f.coeff i) = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.mpr (hcoeff i hi)
      simp [coeff_X_pow, hi, hc]
  let p : R[X] := f.comp (X * (X - 1))
  have hp : p.Monic := hf.comp (monic_X.mul (monic_X_sub_C 1)) (by
    have hdeg := monic_X.natDegree_mul (monic_X_sub_C (1 : R))
    rw [natDegree_X, natDegree_X_sub_C] at hdeg
    have hdeg' : (X * (X - 1) : R[X]).natDegree = 2 := by
      simpa only [map_one] using hdeg
    exact hdeg'.trans_ne (by decide))
  have hpb : aeval b p = 0 := by
    simpa [p, aeval_comp] using hfb
  have hpbar : p.map (residue R) =
      X ^ f.natDegree * (X - 1) ^ f.natDegree := by
    simp [p, Polynomial.map_comp, hfbar, mul_pow]
  have hcop : IsCoprime (X ^ f.natDegree : (ResidueField R)[X])
      ((X - 1) ^ f.natDegree) := by
    apply IsCoprime.pow
    exact ⟨1, -1, by ring⟩
  obtain ⟨q, r, _, _, hpqr, ⟨c, d, hcd⟩, hq, hr⟩ :=
    lift_coprime_factorization R p hp _ _ (monic_X.pow _)
      ((monic_X_sub_C 1).pow _) hpbar hcop
  let e := aeval b (c * q)
  have he : IsIdempotentElem e := by
    dsimp only [e, IsIdempotentElem]
    nth_rw 2 [eq_sub_iff_add_eq.mpr hcd]
    rw [← map_mul, mul_sub, mul_one, mul_mul_mul_comm, ← hpqr]
    simp [hpb]
  have hqbar : aeval e₀ q = e₀ := by
    have h : aeval e₀ (q.map (residue R)) = aeval e₀ q :=
      aeval_map_algebraMap (ResidueField R) e₀ q
    rw [hq] at h
    simpa [he₀.pow_eq hn] using h.symm
  have hrbar : aeval e₀ r * e₀ = 0 := by
    have h : aeval e₀ (r.map (residue R)) = aeval e₀ r :=
      aeval_map_algebraMap (ResidueField R) e₀ r
    rw [hr] at h
    rw [← h]
    simp only [map_pow, map_sub, aeval_X, map_one]
    obtain ⟨n, hn'⟩ := Nat.exists_eq_succ_of_ne_zero hn
    rw [hn', pow_succ, mul_assoc, sub_mul, one_mul, he₀.eq, sub_self, mul_zero]
  have hid : aeval e₀ (c * q) = e₀ := by
    have h := congrArg (fun z : R[X] => aeval e₀ z * e₀) hcd
    simpa [map_add, map_mul, hqbar, add_mul, mul_assoc, hrbar, he₀.eq] using h
  refine ⟨e, he, ?_⟩
  change π (aeval b (c * q)) = e₀
  rw [← aeval_algHom_apply]
  change aeval (Ideal.Quotient.mk I b) (c * q) = e₀
  rw [hb]
  exact hid

theorem maximalIdeal_map_le_jacobson
    (R : Type u) [CommRing R] [IsLocalRing R]
    (B : Type v) [CommRing B] [Algebra R B] [Algebra.IsIntegral R B] :
    (maximalIdeal R).map (algebraMap R B) ≤ Ideal.jacobson (⊥ : Ideal B) := by
  rw [Ideal.jacobson, le_sInf_iff]
  intro J hJ
  let : J.IsMaximal := hJ.2
  have hmax : (J.comap (algebraMap R B)).IsMaximal :=
    Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := R) J
  apply Ideal.map_le_iff_le_comap.mpr
  exact (eq_maximalIdeal hmax).symm.le

theorem idempotent_eq_zero_of_mem_jacobson
    {B : Type v} [CommRing B] {e : B} (he : IsIdempotentElem e)
    (h : e ∈ Ideal.jacobson (⊥ : Ideal B)) : e = 0 := by
  have hu : IsUnit (e * (-1) + 1) := Ideal.mem_jacobson_bot.mp h (-1)
  apply hu.mul_left_eq_zero.mp
  simp [mul_add, he.eq]

theorem idempotents_eq_of_sub_mem_jacobson
    {B : Type v} [CommRing B] {e f : B}
    (he : IsIdempotentElem e) (hf : IsIdempotentElem f)
    (h : e - f ∈ Ideal.jacobson (⊥ : Ideal B)) : e = f := by
  have h₁ : e * (1 - f) = 0 := by
    apply idempotent_eq_zero_of_mem_jacobson (he.mul hf.one_sub)
    have hm := (Ideal.jacobson (⊥ : Ideal B)).mul_mem_right (1 - f) h
    simpa [sub_mul, hf.mul_one_sub_self] using hm
  have h₂ : f * (1 - e) = 0 := by
    apply idempotent_eq_zero_of_mem_jacobson (hf.mul he.one_sub)
    have hn : f - e ∈ Ideal.jacobson (⊥ : Ideal B) :=
      neg_sub e f ▸ (Ideal.jacobson (⊥ : Ideal B)).neg_mem h
    have hm := (Ideal.jacobson (⊥ : Ideal B)).mul_mem_right (1 - e) hn
    simpa [sub_mul, he.mul_one_sub_self] using hm
  linear_combination h₁ - h₂

/-- The first HenselianLifting assertion, with arbitrary universe for the finite algebra. -/
theorem idempotents_lift_uniquely
    (R : Type u) [CommRing R] [HenselianLocalRing R]
    (B : Type v) [CommRing B] [Algebra R B] [Module.Finite R B]
    (e₀ : B ⧸ (maximalIdeal R).map (algebraMap R B))
    (he₀ : IsIdempotentElem e₀) :
    ∃! e : B, IsIdempotentElem e ∧
      Ideal.Quotient.mk ((maximalIdeal R).map (algebraMap R B)) e = e₀ := by
  obtain ⟨e, he, hmap⟩ := exists_idempotent_lift R B e₀ he₀
  refine ⟨e, ⟨he, hmap⟩, ?_⟩
  intro f hf
  apply idempotents_eq_of_sub_mem_jacobson hf.1 he
  apply maximalIdeal_map_le_jacobson R B
  exact Ideal.Quotient.eq.mp (hf.2.trans hmap.symm)

theorem unramified_hom_ext_of_quotient
    (R : Type u) [CommRing R]
    (A : Type v) [CommRing A] [Algebra R A]
    [Algebra.EssFiniteType R A] [Algebra.FormallyUnramified R A]
    {B : Type*} [CommRing B] [Algebra R B]
    (I : Ideal B) (hI : I ≤ Ideal.jacobson (⊥ : Ideal B))
    (f g : A →ₐ[R] B)
    (h : (Ideal.Quotient.mkₐ R I).comp f = (Ideal.Quotient.mkₐ R I).comp g) :
    f = g := by
  obtain ⟨t, ht, ht1⟩ :=
    (Algebra.FormallyUnramified.iff_exists_tensorProduct (R := R) (S := A)).mp inferInstance
  let δ : A ⊗[R] A →ₐ[R] B := Algebra.TensorProduct.lift f g (fun _ _ => .all _ _)
  have hd : (Ideal.Quotient.mkₐ R I).comp δ =
      ((Ideal.Quotient.mkₐ R I).comp f).comp (Algebra.TensorProduct.lmul' R) := by
    ext a
    · simp [δ]
    · simpa [δ] using (AlgHom.congr_fun h a).symm
  have htmod : Ideal.Quotient.mk I (δ t) = 1 := by
    have hh := AlgHom.congr_fun hd t
    simpa [ht1] using hh
  have hu : IsUnit (δ t) := by
    apply Ideal.isUnit_of_sub_one_mem_jacobson_bot
    apply hI
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    simp [htmod]
  ext a
  apply sub_eq_zero.mp
  apply hu.mul_left_eq_zero.mp
  have hh := congrArg δ (ht a)
  have hz : (g a - f a) * δ t = 0 := by simpa [δ] using hh
  linear_combination -hz

theorem exists_separability_idempotent
    (B C : Type*) [CommRing B] [CommRing C] [Algebra B C]
    [Algebra.EssFiniteType B C] [Algebra.FormallyUnramified B C] :
    ∃ t : C ⊗[B] C, IsIdempotentElem t ∧
      (∀ c, (1 ⊗ₜ[B] c - c ⊗ₜ[B] 1) * t = 0) ∧
      Algebra.TensorProduct.lmul' B t = 1 := by
  obtain ⟨e, he, hsp⟩ : ∃ e, IsIdempotentElem e ∧
      KaehlerDifferential.ideal B C = Ideal.span {e} :=
    (Ideal.isIdempotentElem_iff_of_fg _ (KaehlerDifferential.ideal_fg B C)).mp
      ((Ideal.cotangent_subsingleton_iff _).mp
        (inferInstanceAs (Subsingleton (KaehlerDifferential B C))))
  refine ⟨1 - e, he.one_sub, ?_, ?_⟩
  · intro c
    have hc := KaehlerDifferential.one_smul_sub_smul_one_mem_ideal B c
    rw [hsp, Ideal.mem_span_singleton] at hc
    obtain ⟨d, hd⟩ := hc
    rw [hd, mul_assoc, mul_left_comm, he.mul_one_sub_self, mul_zero]
  · have heJ : e ∈ KaehlerDifferential.ideal B C := by
      rw [hsp]
      exact Ideal.subset_span (by simp)
    have hz : Algebra.TensorProduct.lmul' B e = 0 := heJ
    simp [hz]

theorem surjective_of_residue_approximation
    (R : Type u) [CommRing R] [IsLocalRing R]
    {B C : Type*} [CommRing B] [CommRing C] [Algebra R B] [Algebra R C]
    [Module.Finite R C] (f : B →ₐ[R] C)
    (h : ∀ c : C, ∃ b : B, c - f b ∈ (maximalIdeal R).map (algebraMap R C)) :
    Function.Surjective f := by
  change Function.Surjective f.toLinearMap
  apply LinearMap.range_eq_top.mp
  apply top_le_iff.mp
  apply Submodule.le_of_le_smul_of_le_jacobson_bot Module.Finite.fg_top
    (IsLocalRing.maximalIdeal_le_jacobson ⊥)
  intro c _
  obtain ⟨b, hb⟩ := h c
  apply Submodule.mem_sup.mpr
  refine ⟨f b, ⟨b, rfl⟩, c - f b, ?_, by abel⟩
  rwa [Ideal.smul_top_eq_map]

theorem etale_algebraMap_bijective_of_surjective
    (B C : Type*) [CommRing B] [CommRing C] [Algebra B C] [Algebra.Etale B C]
    (hs : Function.Surjective (algebraMap B C))
    (hk : RingHom.ker (algebraMap B C) ≤ Ideal.jacobson (⊥ : Ideal B)) :
    Function.Bijective (algebraMap B C) := by
  refine ⟨(RingHom.injective_iff_ker_eq_bot _).mpr ?_, hs⟩
  obtain ⟨e, he, hsp⟩ :=
    (Ideal.isIdempotentElem_iff_of_fg _
      (Algebra.FinitePresentation.ker_fG_of_surjective (Algebra.ofId B C) hs)).mp
      ((Algebra.FormallyEtale.iff_of_surjective hs).mp inferInstance)
  change RingHom.ker (algebraMap B C) = Ideal.span {e} at hsp
  have heJ : e ∈ Ideal.jacobson (⊥ : Ideal B) := by
    apply hk
    rw [hsp]
    exact Ideal.subset_span (by simp)
  rw [hsp, idempotent_eq_zero_of_mem_jacobson he heJ]
  simp

theorem finiteEtale_section_lift
    (R : Type u) [CommRing R] [HenselianLocalRing R]
    (B C : Type v) [CommRing B] [CommRing C]
    [Algebra R B] [Algebra R C] [Algebra B C] [IsScalarTower R B C]
    [Module.Finite R B] [Module.Finite B C] [Algebra.Etale B C]
    (σ : C →ₐ[B] B ⧸ (maximalIdeal R).map (algebraMap R B)) :
    ∃ ψ : C →ₐ[B] B,
      (Ideal.Quotient.mkₐ B ((maximalIdeal R).map (algebraMap R B))).comp ψ = σ := by
  let I := (maximalIdeal R).map (algebraMap R B)
  let J := (maximalIdeal R).map (algebraMap R C)
  have hIJ : I.map (algebraMap B C) = J := by
    simp only [I, J, Ideal.map_map, IsScalarTower.algebraMap_eq R B C]
  have hle : I ≤ J.comap (algebraMap B C) := by
    rw [← hIJ]
    exact Ideal.le_comap_map
  let π : C →ₐ[B] C ⧸ J := Ideal.Quotient.mkₐ B J
  let j : B ⧸ I →ₐ[B] C ⧸ J := Ideal.quotientMapₐ J (Algebra.ofId B C) hle
  have hσJ : ∀ c ∈ J, σ c = 0 := by
    change J ≤ RingHom.ker σ.toRingHom
    rw [← hIJ]
    apply Ideal.map_le_iff_le_comap.mpr
    intro b hb
    change σ (algebraMap B C b) = 0
    rw [σ.commutes]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hb
  let σ₀ : C ⧸ J →ₐ[B] B ⧸ I := Ideal.Quotient.liftₐ J σ hσJ
  have hσπ : σ₀.comp π = σ := Ideal.Quotient.liftₐ_comp J σ hσJ
  have hσj : σ₀.comp j = AlgHom.id B (B ⧸ I) := by
    ext b
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
    exact σ.commutes b
  obtain ⟨t, ht, htrel, ht1⟩ := exists_separability_idempotent B C
  let δ : C ⊗[B] C →ₐ[B] C ⧸ J :=
    Algebra.TensorProduct.lift (j.comp σ) π (fun _ _ => .all _ _)
  have hδ : σ₀.comp δ = σ.comp (Algebra.TensorProduct.lmul' B) := by
    ext c
    · have h := AlgHom.congr_fun hσj (σ c)
      simpa [δ] using h
    · simpa [δ] using AlgHom.congr_fun hσπ c
  have htσ : σ₀ (δ t) = 1 := by
    have h := AlgHom.congr_fun hδ t
    simpa [ht1] using h
  have hrel (c : C) : (π c - j (σ c)) * δ t = 0 := by
    have h := congrArg δ (htrel c)
    simpa [δ] using h
  have : Module.Finite R C := Module.Finite.trans B C
  obtain ⟨e, he, hebar⟩ := exists_idempotent_lift R C (δ t) (ht.map δ)
  change π e = δ t at hebar
  have hσe : σ e = 1 := by
    exact (congrArg σ₀ hebar).trans htσ
  let D := Localization.Away e
  let ι : C →ₐ[B] D := IsScalarTower.toAlgHom B C D
  have hιsurj : Function.Surjective ι :=
    IsLocalization.Away.algebraMap_surjective_of_isIdempotentElem e he
  have hιe : ι e = 1 :=
    (IsIdempotentElem.iff_eq_one_of_isUnit (IsLocalization.Away.algebraMap_isUnit e)).mp
      (he.map ι)
  let β : D →ₐ[B] B ⧸ I := IsLocalization.Away.liftAlgHom e
    (show IsUnit (σ e) from hσe ▸ isUnit_one)
  have : Module.Finite C D := Module.Finite.of_surjective
    (Algebra.linearMap C D) hιsurj
  have : Module.Finite R D := Module.Finite.trans C D
  have : Algebra.Etale C D := Algebra.Etale.of_isLocalizationAway e
  have : Algebra.Etale B D := Algebra.Etale.comp B C D
  have hBD : Function.Surjective (algebraMap B D) := by
    apply surjective_of_residue_approximation R (IsScalarTower.toAlgHom R B D)
    intro x
    obtain ⟨c, rfl⟩ := hιsurj x
    obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective (σ c)
    refine ⟨b, ?_⟩
    have hc : (c - algebraMap B C b) * e ∈ J := by
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      change (π c - π (algebraMap B C b)) * π e = 0
      have hjb : π (algebraMap B C b) = j (σ c) := by
        rw [← hb]
        rfl
      rw [hjb, hebar]
      exact hrel c
    have hm := Ideal.mem_map_of_mem ι.toRingHom hc
    have hJD : J.map ι.toRingHom = (maximalIdeal R).map (algebraMap R D) := by
      simp only [J, Ideal.map_map]
      rfl
    rw [hJD] at hm
    simpa [map_mul, map_sub, hιe, IsScalarTower.algebraMap_apply B C D] using hm
  have hbij : Function.Bijective (algebraMap B D) := by
    apply etale_algebraMap_bijective_of_surjective B D hBD
    intro b hb
    apply maximalIdeal_map_le_jacobson R B
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    have h := congrArg β (show algebraMap B D b = 0 from hb)
    simpa using h
  let ε : B ≃ₐ[B] D := AlgEquiv.ofBijective (Algebra.ofId B D) hbij
  refine ⟨ε.symm.toAlgHom.comp ι, ?_⟩
  have hβ : (Ideal.Quotient.mkₐ B I).comp ε.symm.toAlgHom = β := by
    apply AlgHom.ext
    intro x
    obtain ⟨b, rfl⟩ := hBD x
    simp [ε]
  rw [← AlgHom.comp_assoc, hβ]
  ext c
  simp [β, ι]

theorem finiteEtale_hom_lift
    (R : Type u) [CommRing R] [HenselianLocalRing R]
    (A B : Type v) [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    [Module.Finite R A] [Module.Finite R B] [Algebra.Etale R A]
    (φ : A →ₐ[R] B ⧸ (maximalIdeal R).map (algebraMap R B)) :
    ∃! f : A →ₐ[R] B,
      (Ideal.Quotient.mkₐ R ((maximalIdeal R).map (algebraMap R B))).comp f = φ := by
  let C := B ⊗[R] A
  let σ : C →ₐ[B] B ⧸ (maximalIdeal R).map (algebraMap R B) :=
    Algebra.TensorProduct.lift (Algebra.ofId B _) φ (fun _ _ => .all _ _)
  obtain ⟨ψ, hψ⟩ := finiteEtale_section_lift R B C σ
  let f : A →ₐ[R] B := (ψ.restrictScalars R).comp Algebra.TensorProduct.includeRight
  have hf : (Ideal.Quotient.mkₐ R ((maximalIdeal R).map (algebraMap R B))).comp f = φ := by
    ext a
    have h := AlgHom.congr_fun hψ (1 ⊗ₜ[R] a)
    change Ideal.Quotient.mk _ (ψ (1 ⊗ₜ[R] a)) = φ a
    refine h.trans ?_
    exact (Algebra.TensorProduct.lift_tmul (Algebra.ofId B _) φ
      (fun _ _ => .all _ _) 1 a).trans (by simp)
  refine ⟨f, hf, ?_⟩
  intro g hg
  exact unramified_hom_ext_of_quotient R A _ (maximalIdeal_map_le_jacobson R B)
    g f (hg.trans hf.symm)

theorem isCoprime_of_residue_monic
    (R : Type u) [CommRing R] [IsLocalRing R]
    (p q : R[X]) (hp : p.Monic)
    (h : IsCoprime (p.map (residue R)) (q.map (residue R))) : IsCoprime p q := by
  apply (Polynomial.isUnit_resultant_iff_isCoprime hp).mp
  apply (residue_ne_zero_iff_isUnit _).mp
  rw [← Polynomial.resultant_map_map]
  have hm := hp.natDegree_map (residue R)
  rw [← hm]
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le
    (show (q.map (residue R)).natDegree ≤ q.natDegree from natDegree_map_le)
  rw [hd, Polynomial.resultant_add_right_deg _ _ _ _ _ le_rfl]
  rw [(hp.map (residue R)).coeff_natDegree, one_pow, one_mul]
  exact ((Polynomial.isUnit_resultant_iff_isCoprime (hp.map (residue R))).mpr h).ne_zero

theorem etale_adjoinRoot_of_separable
    (R : Type u) [CommRing R] (p : R[X]) (hp : p.Monic) (hsep : p.Separable) :
    Algebra.Etale R (AdjoinRoot p) := by
  let P : StandardEtalePair R := ⟨p, hp, p.derivative, 1, 0, 1, by simp⟩
  obtain ⟨c, d, hcd⟩ := hsep
  have hu : IsUnit (AdjoinRoot.mk p p.derivative) := by
    apply isUnit_iff_exists_inv.mpr
    refine ⟨AdjoinRoot.mk p d, ?_⟩
    have h := congrArg (AdjoinRoot.mk p) hcd
    simpa [map_add, map_mul, AdjoinRoot.mk_self, mul_comm] using h
  let e : P.Ring ≃ₐ[R] AdjoinRoot p := P.equivAwayAdjoinRoot.trans
    ((IsLocalization.atUnit (AdjoinRoot p) (Localization.Away (AdjoinRoot.mk p p.derivative))
      _ hu).symm.restrictScalars R)
  exact Algebra.Etale.of_equiv e

theorem exists_monic_separable_lift
    (R : Type u) [CommRing R] [IsLocalRing R]
    (p₀ : (ResidueField R)[X]) (hp₀ : p₀.Monic) (hs₀ : p₀.Separable) :
    ∃ p : R[X], p.Monic ∧ p.Separable ∧ p.map (residue R) = p₀ := by
  have hlift : p₀ ∈ Polynomial.lifts (residue R) :=
    (Polynomial.mem_lifts p₀).mpr (Polynomial.map_surjective _ residue_surjective p₀)
  obtain ⟨p, hmap, _, hp⟩ := Polynomial.lifts_and_degree_eq_and_monic hlift hp₀
  refine ⟨p, hp, ?_, hmap⟩
  apply isCoprime_of_residue_monic R p p.derivative hp
  simpa [← derivative_map, hmap] using (separable_def p₀).mp hs₀

noncomputable def adjoinRoot_residue_equiv
    (R : Type u) [CommRing R] [IsLocalRing R] (p : R[X]) :
    ResidueField R ⊗[R] AdjoinRoot p ≃ₐ[ResidueField R]
      AdjoinRoot (p.map (residue R)) := by
  have : IsScalarTower R (ResidueField R) (ResidueField R ⊗[R] AdjoinRoot p) :=
    IsScalarTower.of_algebraMap_eq' rfl
  let ε : (AdjoinRoot p ⧸ (maximalIdeal R).map (algebraMap R (AdjoinRoot p))) ≃ₐ[R]
      AdjoinRoot (p.map (residue R)) := AdjoinRoot.quotEquivQuotMap p (maximalIdeal R)
  let η : ResidueField R ⊗[R] AdjoinRoot p ≃ₐ[R] AdjoinRoot (p.map (residue R)) :=
    ((Algebra.TensorProduct.quotIdealMapEquivQuotTensor (AdjoinRoot p) (maximalIdeal R)).symm.restrictScalars R).trans ε
  exact AlgEquiv.extendScalarsOfSurjective (R := R) (S := ResidueField R)
    (show Function.Surjective (algebraMap R (ResidueField R)) from residue_surjective) η

theorem exists_finiteEtale_field_lift
    (R : Type u) [CommRing R] [IsLocalRing R]
    (L : Type u) [Field L] [Algebra (ResidueField R) L]
    [Module.Finite (ResidueField R) L] [Algebra.IsSeparable (ResidueField R) L] :
    ∃ A : CommAlgCat.FiniteEtale.{u} R,
      Nonempty (ResidueField R ⊗[R] A ≃ₐ[ResidueField R] L) := by
  let pb := Field.powerBasisOfFiniteOfSeparable (ResidueField R) L
  let p₀ := minpoly (ResidueField R) pb.gen
  have hp₀ : p₀.Monic := minpoly.monic (Algebra.IsIntegral.isIntegral pb.gen)
  have hs₀ : p₀.Separable := Algebra.IsSeparable.isSeparable (ResidueField R) pb.gen
  obtain ⟨p, hp, hs, hmap⟩ := exists_monic_separable_lift R p₀ hp₀ hs₀
  have : Module.Finite R (AdjoinRoot p) := hp.finite_adjoinRoot
  have : Algebra.Etale R (AdjoinRoot p) := etale_adjoinRoot_of_separable R p hp hs
  refine ⟨CommAlgCat.FiniteEtale.of R (AdjoinRoot p), ⟨?_⟩⟩
  refine (adjoinRoot_residue_equiv R p).trans ?_
  refine (AdjoinRoot.algEquivOfEq (ResidueField R) _ _ hmap).trans ?_
  exact AdjoinRoot.equiv' p₀ pb (by simp [p₀, AdjoinRoot.aeval_eq]) (minpoly.aeval _ _)

theorem exists_finiteEtale_lift
    (R : Type u) [CommRing R] [IsLocalRing R]
    (S : Type u) [CommRing S] [Algebra (ResidueField R) S]
    [Algebra.Etale (ResidueField R) S] :
    ∃ A : CommAlgCat.FiniteEtale.{u} R,
      Nonempty (ResidueField R ⊗[R] A ≃ₐ[ResidueField R] S) := by
  classical
  obtain ⟨ι, _, L, _, _, ε, hL⟩ :=
    (Algebra.Etale.iff_exists_algEquiv_prod (ResidueField R) S).mp inferInstance
  let := Fintype.ofFinite ι
  have hLift (i : ι) : ∃ A : CommAlgCat.FiniteEtale.{u} R,
      Nonempty (ResidueField R ⊗[R] A ≃ₐ[ResidueField R] L i) := by
    have := (hL i).1
    have := (hL i).2
    exact exists_finiteEtale_field_lift R (L i)
  choose A hA using hLift
  let e (i : ι) := Classical.choice (hA i)
  refine ⟨CommAlgCat.FiniteEtale.of R (∀ i, A i), ⟨?_⟩⟩
  exact (Algebra.TensorProduct.piRight R (ResidueField R) (ResidueField R) (fun i => A i)).trans
    ((AlgEquiv.piCongrRight e).trans ε.symm)

theorem finiteEtale_baseChange_hom_bijective
    (R : Type u) [CommRing R] [HenselianLocalRing R]
    (A B : Type u) [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    [Module.Finite R A] [Module.Finite R B] [Algebra.Etale R A] :
    Function.Bijective (fun f : A →ₐ[R] B =>
      (Algebra.TensorProduct.map (AlgHom.id (ResidueField R) (ResidueField R)) f :
        ResidueField R ⊗[R] A →ₐ[ResidueField R] ResidueField R ⊗[R] B)) := by
  let I := (maximalIdeal R).map (algebraMap R B)
  let : Algebra (ResidueField R) (B ⧸ I) :=
    Ideal.Quotient.algebraQuotientOfLEComap Ideal.le_comap_map
  have : IsScalarTower R (ResidueField R) (B ⧸ I) :=
    IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower R (ResidueField R) (ResidueField R ⊗[R] B) :=
    IsScalarTower.of_algebraMap_eq' rfl
  let ε : (B ⧸ I) ≃ₐ[ResidueField R] ResidueField R ⊗[R] B :=
    Algebra.TensorProduct.quotIdealMapEquivQuotTensor B (maximalIdeal R)
  have hε (b : B) : ε (Ideal.Quotient.mk I b) = (1 : ResidueField R) ⊗ₜ[R] b :=
    Algebra.TensorProduct.quotIdealMapEquivQuotTensor_mk B (maximalIdeal R) b
  constructor
  · intro f g h
    apply unramified_hom_ext_of_quotient R A I (maximalIdeal_map_le_jacobson R B) f g
    ext a
    apply ε.injective
    change ε (Ideal.Quotient.mk I (f a)) = ε (Ideal.Quotient.mk I (g a))
    rw [hε, hε]
    have hh := AlgHom.congr_fun h (1 ⊗ₜ[R] a)
    simpa using hh
  · intro φ
    let φ₀ : A →ₐ[R] B ⧸ I := (ε.symm.toAlgHom.restrictScalars R).comp
      ((φ.restrictScalars R).comp Algebra.TensorProduct.includeRight)
    obtain ⟨f, hf, _⟩ := finiteEtale_hom_lift R A B φ₀
    refine ⟨f, ?_⟩
    apply Algebra.TensorProduct.ext_ring
    ext a
    have hh := congrArg ε (AlgHom.congr_fun hf a)
    have hh' : ε (Ideal.Quotient.mk I (f a)) = φ (1 ⊗ₜ[R] a) := by
      simpa [φ₀] using hh
    rw [hε] at hh'
    simpa using hh'

/-- The second HenselianLifting assertion: the actual residue base-change functor is an equivalence. -/
theorem finiteEtale_residue_isEquivalence
    (R : Type u) [CommRing R] [HenselianLocalRing R] :
    (CommAlgCat.FiniteEtale.baseChange R (ResidueField R) :
      CommAlgCat.FiniteEtale.{u} R ⥤ CommAlgCat.FiniteEtale.{u} (ResidueField R)).IsEquivalence := by
  let F : CommAlgCat.FiniteEtale.{u} R ⥤ CommAlgCat.FiniteEtale.{u} (ResidueField R) :=
    CommAlgCat.FiniteEtale.baseChange R (ResidueField R)
  have hbij (A B : CommAlgCat.FiniteEtale.{u} R) :
      Function.Bijective (F.map : (A ⟶ B) → (F.obj A ⟶ F.obj B)) := by
    have h := finiteEtale_baseChange_hom_bijective R A B
    constructor
    · intro f g hfg
      apply CategoryTheory.ObjectProperty.hom_ext
      apply CommAlgCat.hom_ext
      apply h.1
      exact congrArg (fun f => f.hom.hom) hfg
    · intro f
      obtain ⟨g, hg⟩ := h.2 f.hom.hom
      refine ⟨CommAlgCat.FiniteEtale.ofHom g, ?_⟩
      apply CategoryTheory.ObjectProperty.hom_ext
      apply CommAlgCat.hom_ext
      exact hg
  have : F.Faithful := ⟨fun {A B} => (hbij A B).1⟩
  have : F.Full := ⟨fun {A B} => (hbij A B).2⟩
  have : F.EssSurj := ⟨fun S => by
    obtain ⟨A, ⟨e⟩⟩ := exists_finiteEtale_lift R S
    exact ⟨A, ⟨CommAlgCat.FiniteEtale.isoMk e⟩⟩⟩
  show F.IsEquivalence
  exact ⟨inferInstance, inferInstance, inferInstance⟩

end OAI.Algebra.LocalRing.HenselianLifting.Construction
