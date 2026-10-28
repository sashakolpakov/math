import Mathlib

/-! # Witt Finite -/

namespace OAI

noncomputable section

namespace NumberTheory.PadicHodge.WeakAdmissibility.WittFinite.Pi

/-! Products of complete modules for a principal adic filtration. -/

variable {R ι : Type*} [CommRing R] (q : R)

theorem mem_power_smul_pi (n : ℕ) (x : ι → R) :
    x ∈ (Ideal.span {q}) ^ n • (⊤ : Submodule R (ι → R)) ↔ ∀ i, q ^ n ∣ x i := by
  rw [Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul,
    Submodule.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨y, _, hy⟩ i
    exact ⟨y i, (congrFun hy i).symm⟩
  · intro hx
    choose y hy using hx
    refine ⟨y, Submodule.mem_top, ?_⟩
    funext i
    exact (hy i).symm

instance piPrecomplete [IsPrecomplete (Ideal.span {q}) R] :
    IsPrecomplete (Ideal.span {q}) (ι → R) where
  prec' f hf := by
    have hcoord (i : ι) : ∀ {m n : ℕ}, m ≤ n →
        f m i ≡ f n i [SMOD (Ideal.span {q}) ^ m • (⊤ : Submodule R R)] := by
      intro m n hmn
      have he := hf hmn
      rw [SModEq.sub_mem, mem_power_smul_pi] at he
      rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
      exact he i
    have hlim (i : ι) : ∃ L : R, ∀ n, f n i ≡ L [SMOD (Ideal.span {q}) ^ n • (⊤ : Submodule R R)] :=
      IsPrecomplete.prec (show IsPrecomplete (Ideal.span {q}) R from inferInstance) (hcoord i)
    choose L hL using hlim
    refine ⟨L, fun n => ?_⟩
    rw [SModEq.sub_mem, mem_power_smul_pi]
    intro i
    have he := hL i n
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at he
    exact he

instance piHausdorff [IsHausdorff (Ideal.span {q}) R] :
    IsHausdorff (Ideal.span {q}) (ι → R) where
  haus' x hx := by
    funext i
    apply IsHausdorff.haus (show IsHausdorff (Ideal.span {q}) R from inferInstance)
    intro n
    have he := hx n
    rw [SModEq.sub_mem, sub_zero, mem_power_smul_pi] at he
    rw [SModEq.sub_mem, sub_zero, smul_eq_mul, Ideal.mul_top,
      Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    exact he i

instance piComplete [IsAdicComplete (Ideal.span {q}) R] :
    IsAdicComplete (Ideal.span {q}) (ι → R) where

end NumberTheory.PadicHodge.WeakAdmissibility.WittFinite.Pi

namespace NumberTheory.PadicHodge.WeakAdmissibility.WittFinite

/-! Finite generation of finite-residue Witt rings over the actual p-adic integers. -/

open _root_.Module
variable (p : ℕ) [Fact p.Prime]
variable (k : Type*) [Field k] [Fintype k] [CharP k p]

instance residueAlgebra : Algebra (ZMod p) k :=
  (ZMod.castHom (dvd_refl p) k).toAlgebra

def padicToWitt : ℤ_[p] →+* WittVector p k :=
  (WittVector.map (ZMod.castHom (dvd_refl p) k)).comp (WittVector.equiv p).symm.toRingHom

instance wittAlgebra : Algebra ℤ_[p] (WittVector p k) := (padicToWitt p k).toAlgebra

instance padicComplete : IsAdicComplete (Ideal.span {(p : ℤ_[p])}) ℤ_[p] := by
  rw [← PadicInt.maximalIdeal_eq_span_p]
  infer_instance

instance wittComplete : IsAdicComplete (Ideal.span {(p : ℤ_[p])}) (WittVector p k) := by
  apply (IsAdicComplete.map_algebraMap_iff (S := WittVector p k)
    (Ideal.span {(p : ℤ_[p])}) (WittVector p k)).mp
  rw [Ideal.map_span, Set.image_singleton, map_natCast]
  infer_instance

def padicResidue : ℤ_[p] →+* ZMod p :=
  WittVector.constantCoeff.comp (WittVector.equiv p).symm.toRingHom

def residueLift (a : ZMod p) : ℤ_[p] :=
  WittVector.equiv p (WittVector.teichmuller p a)

theorem padicResidue_lift (a : ZMod p) : padicResidue p (residueLift p a) = a := by
  simp [padicResidue, residueLift, WittVector.constantCoeff_apply]

omit [Fintype k] in
theorem padicToWitt_coeff_zero (a : ℤ_[p]) :
    (padicToWitt p k a).coeff 0 = algebraMap (ZMod p) k (padicResidue p a) := by
  rfl

variable {ι : Type*} [Fintype ι]

def liftedCombination (b : Basis ι (ZMod p) k) : (ι → ℤ_[p]) →ₗ[ℤ_[p]] WittVector p k where
  toFun a := ∑ i, a i • WittVector.teichmuller p (b i)
  map_add' a c := by simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' a c := by simp only [Pi.smul_apply, smul_smul, Finset.smul_sum, RingHom.id_apply, smul_eq_mul]

omit [Fintype k] in
theorem liftedCombination_coeff_zero (b : Basis ι (ZMod p) k) (a : ι → ℤ_[p]) :
    (liftedCombination p k b a).coeff 0 = ∑ i, padicResidue p (a i) • b i := by
  change WittVector.constantCoeff (∑ i, a i • WittVector.teichmuller p (b i)) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Algebra.smul_def, map_mul]
  change (padicToWitt p k (a i)).coeff 0 * (WittVector.teichmuller p (b i)).coeff 0 = _
  rw [padicToWitt_coeff_zero, WittVector.teichmuller_coeff_zero, Algebra.smul_def]

theorem liftedCombination_modp (b : Basis ι (ZMod p) k) :
    Function.Surjective ((Submodule.mkQ
      ((Ideal.span {(p : ℤ_[p])}) • (⊤ : Submodule ℤ_[p] (WittVector p k)))) ∘ₗ
        liftedCombination p k b) := by
  intro x
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ x
  let a : ι → ℤ_[p] := fun i => residueLift p (b.repr (x.coeff 0) i)
  refine ⟨a, ?_⟩
  change Submodule.mkQ _ (liftedCombination p k b a) = Submodule.mkQ _ x
  apply (Submodule.Quotient.eq _).mpr
  have hc : (liftedCombination p k b a - x).coeff 0 = 0 := by
    change WittVector.constantCoeff (liftedCombination p k b a - x) = 0
    rw [map_sub]
    change (liftedCombination p k b a).coeff 0 - x.coeff 0 = 0
    rw [liftedCombination_coeff_zero]
    simp only [a, padicResidue_lift, b.sum_repr, sub_self]
  have hm := (WittVector.mem_span_p_iff_coeff_zero_eq_zero _).mpr hc
  rw [Ideal.mem_span_singleton] at hm
  obtain ⟨z, hz⟩ := hm
  rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists]
  refine ⟨z, Submodule.mem_top, ?_⟩
  simpa only [Algebra.smul_def, map_natCast] using hz.symm

theorem liftedCombination_surjective (b : Basis ι (ZMod p) k) :
    Function.Surjective (liftedCombination p k b) :=
  surjective_of_mkQ_comp_surjective (I := Ideal.span {(p : ℤ_[p])})
    (liftedCombination_modp p k b)

instance wittFinite : Module.Finite ℤ_[p] (WittVector p k) :=
  Module.Finite.of_surjective (liftedCombination p k (Module.finBasis (ZMod p) k))
    (liftedCombination_surjective p k _)

end NumberTheory.PadicHodge.WeakAdmissibility.WittFinite

end

end OAI
