import OAI.NumberTheory.PadicHodge.IntegralComparison.DegreeNatural
import OAI.NumberTheory.PadicHodge.IntegralComparison.Finite.PolynomialCoordinates

/-! # Degree Base Change -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Polynomial.DegreeBaseChange.Law

noncomputable section

section

/-! A compatible multiplicative geometric degree law on a polynomial
algebra, obtained from finite families of powers of one actual endomorphism. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.DegreeNatural.LawScalarExtension OAI.NumberTheory.PadicHodge.IntegralComparison.Finite.PolynomialCoordinates

variable {K : Type} [Field K] [IsAlgClosed K]
  (A : Over (Spec (CommRingCat.of K))) [GrpObj A] [IsCommMonObj A]
  [IsProper A.hom] [Smooth A.hom] [GeometricallyIntegral A.hom]
  (L : Type*) [CommRing L] [Algebra ℚ L] (F : AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd A)

local instance : IsIntegral A.left :=
  GeometricallyIntegral.isIntegral_of_subsingleton A.hom

def valueBound (n : ℕ) (P : Polynomial L) : L :=
  DegreeNatural.LawScalarExtension.value A L (fun i : Fin (n + 1) => F ^ (i : ℕ)) (fun i => P.coeff i)

theorem valueBound_mono (P : Polynomial L) (n m : ℕ)
    (hn : P.natDegree ≤ n) (hnm : n ≤ m) :
    valueBound A L F n P = valueBound A L F m P := by
  classical
  let e : Fin (n + 1) → Fin (m + 1) := Fin.castLE (Nat.succ_le_succ hnm)
  have h := DegreeNatural.LawScalarExtension.value_pushforward A L (fun i : Fin (m + 1) => F ^ (i : ℕ)) e 0
    (by simp only [e, Fin.val_castLE, Fin.val_zero, pow_zero]) (fun i => P.coeff i)
  have hc : (fun k : Fin (m + 1) => ∑ i : Fin (n + 1),
      if k = e i then P.coeff i else 0) = fun k : Fin (m + 1) => P.coeff k := by
    funext k
    have he (i : Fin (n + 1)) : k = e i ↔ (i : ℕ) = k := by
      simp only [Fin.ext_iff, e, Fin.val_castLE, eq_comm]
    simp_rw [he]
    exact (Finite.PolynomialCoordinates.coeff_expansion P n hn k).symm
  rw [hc] at h
  exact h

def norm (P : Polynomial L) : L := valueBound A L F P.natDegree P

theorem norm_eq_valueBound (P : Polynomial L) (n : ℕ) (hn : P.natDegree ≤ n) :
    norm A L F P = valueBound A L F n P :=
  valueBound_mono A L F P P.natDegree n le_rfl hn

theorem valueBound_mul (P Q : Polynomial L) (n m : ℕ)
    (hn : P.natDegree ≤ n) (hm : Q.natDegree ≤ m) :
    valueBound A L F (n + m) (P * Q) = valueBound A L F n P * valueBound A L F m Q := by
  classical
  let e : Fin (n + 1) × Fin (m + 1) → Fin (n + m + 1) :=
    fun t => ⟨t.1.val + t.2.val, by have := t.1.isLt; have := t.2.isLt; omega⟩
  have h := DegreeNatural.LawScalarExtension.value_pushforward A L (fun i : Fin (n + m + 1) => F ^ (i : ℕ)) e (0, 0)
    (by simp only [e, Fin.val_zero, zero_add, pow_zero])
    (fun t => P.coeff t.1 * Q.coeff t.2)
  have hc : (fun k : Fin (n + m + 1) => ∑ t : Fin (n + 1) × Fin (m + 1),
      if k = e t then P.coeff t.1 * Q.coeff t.2 else 0) =
        fun k : Fin (n + m + 1) => (P * Q).coeff k := by
    funext k
    have he (t : Fin (n + 1) × Fin (m + 1)) :
        k = e t ↔ t.1.val + t.2.val = k := by simp only [Fin.ext_iff, e, eq_comm]
    simp_rw [he]
    exact (Finite.PolynomialCoordinates.coeff_product_expansion P Q n m hn hm k).symm
  rw [hc] at h
  have he : (fun t : Fin (n + 1) × Fin (m + 1) => F ^ (e t : ℕ)) =
      (fun t => F ^ (t.1 : ℕ) * F ^ (t.2 : ℕ)) := by
    funext t
    exact pow_add F _ _
  rw [he] at h
  change _ = valueBound A L F (n + m) (P * Q) at h
  rw [← h]
  exact DegreeNatural.LawScalarExtension.value_mul A L (fun i : Fin (n + 1) => F ^ (i : ℕ))
    (fun j : Fin (m + 1) => F ^ (j : ℕ)) 0 (by simp) 0 (by simp)
    (fun i => P.coeff i) (fun j => Q.coeff j)

theorem norm_mul (P Q : Polynomial L) : norm A L F (P * Q) = norm A L F P * norm A L F Q := by
  rw [norm_eq_valueBound A L F (P * Q) (P.natDegree + Q.natDegree) Polynomial.natDegree_mul_le]
  exact valueBound_mul A L F P Q P.natDegree Q.natDegree le_rfl le_rfl

theorem norm_one : norm A L F 1 = 1 := by
  rw [norm_eq_valueBound A L F 1 0 (by simp)]
  have hs : (∑ i : Fin 1, (1 : ℕ) • F ^ (i : ℕ)) = 1 := by simp
  have : IsFinite (∑ i : Fin 1, (1 : ℕ) • F ^ (i : ℕ)).toMul.hom.hom.left := by
    rw [hs]
    change IsFinite (𝟙 A.left)
    infer_instance
  have : IsDominant (∑ i : Fin 1, (1 : ℕ) • F ^ (i : ℕ)).toMul.hom.hom.left := by
    rw [hs]
    change IsDominant (𝟙 A.left)
    infer_instance
  have h := DegreeNatural.LawScalarExtension.value_nat A L (fun i : Fin 1 => F ^ (i : ℕ)) (fun _ => 1)
  rw [hs] at h
  change DegreeNatural.LawScalarExtension.value A L _ _ = ((𝟙 A.left : A.left ⟶ A.left).residueDegree (genericPoint A.left) : L) at h
  simpa only [valueBound, Polynomial.coeff_one, Fin.fin_one_eq_zero,
    Fin.val_zero, ite_true, Nat.cast_one, Scheme.Hom.residueDegree_id] using h

def normHom : Polynomial L →* L where
  toFun := norm A L F
  map_one' := norm_one A L F
  map_mul' := norm_mul A L F

end

/-! The polynomial-algebra degree law commutes with coefficient-ring
homomorphisms. In particular its values on scalar shifts form an actual
rational polynomial. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.DegreeNatural.LawScalarExtension OAI.NumberTheory.PadicHodge.IntegralComparison.Endomorphism.DegreeLaw

variable {K : Type} [Field K] [IsAlgClosed K]
  (A : Over (Spec (CommRingCat.of K))) [GrpObj A] [IsCommMonObj A]
  [IsProper A.hom] [Smooth A.hom] [GeometricallyIntegral A.hom]

theorem norm_map (L M : Type*) [CommRing L] [Algebra ℚ L] [CommRing M] [Algebra ℚ M]
    (F : AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd A) (φ : L →ₐ[ℚ] M) (P : Polynomial L) :
    norm A M F (P.map φ.toRingHom) = φ (norm A L F P) := by
  rw [norm_eq_valueBound A M F _ P.natDegree Polynomial.natDegree_map_le]
  unfold norm valueBound DegreeNatural.LawScalarExtension.value
  simp only [Polynomial.coeff_map]
  have hφ : φ.toRingHom.comp (algebraMap ℚ L) = algebraMap ℚ M := RingHom.ext φ.commutes
  have h := MvPolynomial.hom_eval₂
    (Endomorphism.DegreeLaw.degreePolynomial A (fun i : Fin (P.natDegree + 1) => F ^ (i : ℕ)))
    (algebraMap ℚ L) φ.toRingHom (fun i => P.coeff i)
  rw [hφ] at h
  exact h.symm

def plusPolynomial (F : AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd A) : Polynomial ℚ :=
  norm A (Polynomial ℚ) F (Polynomial.C (Polynomial.X : Polynomial ℚ) + Polynomial.X)

theorem plusPolynomial_aeval (L : Type*) [CommRing L] [Algebra ℚ L]
    (F : AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd A) (c : L) :
    Polynomial.aeval c (plusPolynomial A F) =
      norm A L F (Polynomial.C c + Polynomial.X) := by
  have h := norm_map A (Polynomial ℚ) L F (Polynomial.aeval c)
    (Polynomial.C (Polynomial.X : Polynomial ℚ) + Polynomial.X)
  simpa only [Polynomial.map_add, Polynomial.map_C, Polynomial.map_X,
    AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, Polynomial.aeval_X, plusPolynomial] using h.symm

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Polynomial.DegreeBaseChange.Law
