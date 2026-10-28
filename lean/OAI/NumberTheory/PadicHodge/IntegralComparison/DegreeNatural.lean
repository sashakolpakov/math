import OAI.NumberTheory.PadicHodge.IntegralComparison.DegreeCoordinateUniqueness
import OAI.NumberTheory.PadicHodge.IntegralComparison.Endomorphism.DegreeLaw

/-! # Degree Natural -/

namespace OAI

noncomputable section

namespace NumberTheory.PadicHodge.IntegralComparison.DegreeNatural.Coordinates

/-! Compatibility of the actual geometric degree polynomial with
natural integral linear changes of endomorphism coordinates. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.Endomorphism.DegreeLaw OAI.NumberTheory.PadicHodge.IntegralComparison.DegreeCoordinateUniqueness.Endomorphism

def substitution {ι κ : Type*} [Fintype κ] (M : ι → κ → ℕ) :
    MvPolynomial ι ℚ →+* MvPolynomial κ ℚ :=
  MvPolynomial.eval₂Hom MvPolynomial.C
    (fun i => ∑ j, MvPolynomial.C (M i j : ℚ) * MvPolynomial.X j)

theorem eval_substitution {ι κ : Type*} [Fintype κ] (M : ι → κ → ℕ)
    (b : κ → ℕ) (P : MvPolynomial ι ℚ) :
    MvPolynomial.eval (fun j => (b j : ℚ)) (substitution M P) =
      MvPolynomial.eval (fun i => ((∑ j, M i j * b j : ℕ) : ℚ)) P := by
  change MvPolynomial.eval _ (MvPolynomial.eval₂ MvPolynomial.C _ P) = _
  rw [← MvPolynomial.eval_assoc]
  congr 2
  funext i
  simp only [Function.comp_apply, map_sum, map_mul, MvPolynomial.eval_C,
    MvPolynomial.eval_X, Nat.cast_sum, Nat.cast_mul]

theorem combination_eq {G : Type*} [AddCommGroup G] {ι κ : Type*}
    [Fintype ι] [Fintype κ] (f : ι → G) (M : ι → κ → ℕ) (b : κ → ℕ) :
    (∑ i, (∑ j, M i j * b j) • f i) = ∑ j, b j • ∑ i, M i j • f i := by
  calc
    _ = ∑ i, ∑ j, (M i j * b j) • f i := by
      apply Finset.sum_congr rfl
      intro i hi
      exact (Finset.sum_nsmul_assoc _ _ _).symm
    _ = ∑ j, ∑ i, b j • (M i j • f i) := by
      rw [Finset.sum_comm]
      simp only [mul_nsmul]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j hj
      exact Finset.sum_nsmul Finset.univ (b j) (fun i => M i j • f i)

theorem eval₂_substitution {ι κ L : Type*} [Fintype κ] [CommRing L]
    (φ : ℚ →+* L) (M : ι → κ → ℕ) (b : κ → L) (P : MvPolynomial ι ℚ) :
    MvPolynomial.eval₂ φ b (substitution M P) =
      MvPolynomial.eval₂ φ (fun i => ∑ j, (M i j : L) * b j) P := by
  change MvPolynomial.eval₂ φ b (MvPolynomial.eval₂ MvPolynomial.C _ P) = _
  rw [← MvPolynomial.eval₂_assoc]
  congr 1
  funext i
  simp only [MvPolynomial.eval₂_sum, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X]
  apply Finset.sum_congr rfl
  intro j hj
  have he : MvPolynomial.eval₂ φ b (MvPolynomial.C (M i j : ℚ)) = (M i j : L) := by
    rw [MvPolynomial.eval₂_C, map_natCast]
  exact congrArg (fun z => z * b j) he

variable {K : Type} [Field K] [IsAlgClosed K]
  (A : Over (Spec (CommRingCat.of K))) [GrpObj A] [IsCommMonObj A]
  [IsProper A.hom] [Smooth A.hom] [GeometricallyIntegral A.hom]

local instance : IsIntegral A.left :=
  GeometricallyIntegral.isIntegral_of_subsingleton A.hom

theorem degreePolynomial_substitution {ι κ : Type*} [Fintype ι] [Fintype κ]
    (f : ι → AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd A) (g : κ → AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd A)
    (M : ι → κ → ℕ) (hM : ∀ j, g j = ∑ i, M i j • f i)
    (j₀ : κ) (hj₀ : g j₀ = 1) :
    substitution M (Endomorphism.DegreeLaw.degreePolynomial A f) = Endomorphism.DegreeLaw.degreePolynomial A g := by
  apply DegreeCoordinateUniqueness.Endomorphism.eq_of_identity_evals A g j₀ hj₀
  intro b hf hd
  have he : (∑ i, (∑ j, M i j * b j) • f i) = ∑ j, b j • g j := by
    rw [combination_eq]
    simp only [← hM]
  have : IsFinite (∑ j, b j • g j).toMul.hom.hom.left := hf
  have : IsDominant (∑ j, b j • g j).toMul.hom.hom.left := hd
  have : IsFinite (∑ i, (∑ j, M i j * b j) • f i).toMul.hom.hom.left := he.symm ▸ hf
  have : IsDominant (∑ i, (∑ j, M i j * b j) • f i).toMul.hom.hom.left := he.symm ▸ hd
  rw [eval_substitution, Endomorphism.DegreeLaw.degreePolynomial_eval, Endomorphism.DegreeLaw.degreePolynomial_eval, he]

end NumberTheory.PadicHodge.IntegralComparison.DegreeNatural.Coordinates

namespace NumberTheory.PadicHodge.IntegralComparison.DegreeNatural.LawScalarExtension
open _root_.CategoryTheory
open _root_.AlgebraicGeometry
open OAI.NumberTheory.PadicHodge.IntegralComparison.Endomorphism.DegreeLaw
open OAI.NumberTheory.PadicHodge.IntegralComparison.DegreeCoordinateUniqueness.Endomorphism
open OAI.NumberTheory.PadicHodge.IntegralComparison.DegreeNatural.Coordinates
open OAI.NumberTheory.PadicHodge.IntegralComparison.DegreeProductCoordinates
section

/-! Scalar extension of the genuine finite-family degree polynomials,
with the coordinate changes and geometric values kept explicit. -/

variable {K : Type} [Field K] [IsAlgClosed K]
  (A : Over (Spec (CommRingCat.of K))) [GrpObj A] [IsCommMonObj A]
  [IsProper A.hom] [Smooth A.hom] [GeometricallyIntegral A.hom]
  (L : Type*) [CommRing L] [Algebra ℚ L]

local instance : IsIntegral A.left :=
  GeometricallyIntegral.isIntegral_of_subsingleton A.hom

def value {ι : Type*} [Fintype ι] (f : ι → AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd A) (x : ι → L) : L :=
  MvPolynomial.eval₂ (algebraMap ℚ L) x (Endomorphism.DegreeLaw.degreePolynomial A f)

theorem value_nat {ι : Type*} [Fintype ι] (f : ι → AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd A)
    (a : ι → ℕ) [IsFinite (∑ i, a i • f i).toMul.hom.hom.left]
    [IsDominant (∑ i, a i • f i).toMul.hom.hom.left] :
    value A L f (fun i => (a i : L)) =
      ((∑ i, a i • f i).toMul.hom.hom.left.residueDegree (genericPoint A.left) : L) := by
  have h := congrArg (algebraMap ℚ L) (Endomorphism.DegreeLaw.degreePolynomial_eval A f a)
  change (algebraMap ℚ L) (MvPolynomial.eval₂ (RingHom.id ℚ)
    (fun i => (a i : ℚ)) (Endomorphism.DegreeLaw.degreePolynomial A f)) = _ at h
  rw [MvPolynomial.hom_eval₂] at h
  simpa only [value, RingHom.comp_id, map_natCast] using h

theorem value_coordinates {ι κ : Type*} [Fintype ι] [Fintype κ]
    (f : ι → AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd A) (g : κ → AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd A)
    (M : ι → κ → ℕ) (hM : ∀ j, g j = ∑ i, M i j • f i)
    (j₀ : κ) (hj₀ : g j₀ = 1) (x : κ → L) :
    value A L f (fun i => ∑ j, (M i j : L) * x j) = value A L g x := by
  have h := congrArg (MvPolynomial.eval₂ (algebraMap ℚ L) x)
    (Coordinates.degreePolynomial_substitution A f g M hM j₀ hj₀)
  rw [Coordinates.eval₂_substitution] at h
  exact h

theorem value_reindex {ι κ : Type*} [Fintype ι] [Fintype κ]
    (f : κ → AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd A) (e : ι ≃ κ) (j₀ : κ) (hj₀ : f j₀ = 1) (x : ι → L) :
    value A L (fun i => f (e i)) x = value A L f (fun j => x (e.symm j)) := by
  classical
  let M : κ → ι → ℕ := fun i j => if i = e j then 1 else 0
  have hM (j : ι) : f (e j) = ∑ i, M i j • f i := by simp [M]
  have he : (fun i => ∑ j, (M i j : L) * x j) = fun i => x (e.symm i) := by
    funext i
    simp only [M, Nat.cast_ite, Nat.cast_one, Nat.cast_zero, ite_mul, one_mul, zero_mul]
    have ht (j : ι) : i = e j ↔ j = e.symm i := by simp only [eq_comm, Equiv.eq_symm_apply]
    simp only [ht, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  have h := value_coordinates A L f (fun i => f (e i)) M hM (e.symm j₀)
    (by simpa only [Equiv.apply_symm_apply] using hj₀) x
  rw [he] at h
  exact h.symm

theorem value_mul_withIdentity {ι κ : Type*} [Fintype ι] [Fintype κ]
    (f : ι → AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd A) (g : κ → AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd A)
    (a : Option ι → L) (b : Option κ → L) :
    value A L (fun t : Option ι × Option κ => Endomorphism.DegreeUniqueness.withIdentity A f t.1 * Endomorphism.DegreeUniqueness.withIdentity A g t.2)
      (fun t => a t.1 * b t.2) =
      value A L (Endomorphism.DegreeUniqueness.withIdentity A f) a * value A L (Endomorphism.DegreeUniqueness.withIdentity A g) b := by
  let v : Option (Option (ι ⊕ κ)) → L :=
    fun i => Option.elim i (b none) (fun j => Option.elim j (a none)
      (Sum.elim (fun k => a (some k)) (fun k => b (some k))))
  have hl (i : Option ι) : v (DegreeProductCoordinates.leftIndex i) = a i := by cases i <;> rfl
  have hr (i : Option κ) : v (DegreeProductCoordinates.rightIndex i) = b i := by cases i <;> rfl
  have h := congrArg (MvPolynomial.eval₂ (algebraMap ℚ L) v) (Endomorphism.DegreeLaw.degreePolynomial_mul A f g)
  change MvPolynomial.eval₂ (algebraMap ℚ L) v
    (MvPolynomial.eval₂ MvPolynomial.C _ _) = _ at h
  dsimp only [DegreeProductCoordinates.leftSub, DegreeProductCoordinates.rightSub] at h
  rw [← MvPolynomial.eval₂_assoc, MvPolynomial.eval₂_mul,
    MvPolynomial.eval₂_rename, MvPolynomial.eval₂_rename] at h
  simp only [MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X, hl, hr] at h
  change value A L _ _ =
    value A L (Endomorphism.DegreeUniqueness.withIdentity A f) (fun i => v (DegreeProductCoordinates.leftIndex i)) *
      value A L (Endomorphism.DegreeUniqueness.withIdentity A g) (fun i => v (DegreeProductCoordinates.rightIndex i)) at h
  simpa only [hl, hr] using h

theorem value_mul {ι κ : Type*} [Fintype ι] [Fintype κ]
    (f : ι → AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd A) (g : κ → AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd A)
    (i₀ : ι) (hi₀ : f i₀ = 1) (j₀ : κ) (hj₀ : g j₀ = 1)
    (a : ι → L) (b : κ → L) :
    value A L (fun t : ι × κ => f t.1 * g t.2) (fun t => a t.1 * b t.2) =
      value A L f a * value A L g b := by
  classical
  let e := Equiv.optionSubtypeNe i₀
  let d := Equiv.optionSubtypeNe j₀
  let f' : {i // i ≠ i₀} → AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd A := fun i => f i
  let g' : {j // j ≠ j₀} → AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd A := fun j => g j
  have hf (i) : f (e i) = Endomorphism.DegreeUniqueness.withIdentity A f' i := by
    cases i <;> simp only [e, f', Equiv.optionSubtypeNe_none, Equiv.optionSubtypeNe_some,
      Endomorphism.DegreeUniqueness.withIdentity, Option.elim_none, Option.elim_some, hi₀]
  have hg (j) : g (d j) = Endomorphism.DegreeUniqueness.withIdentity A g' j := by
    cases j <;> simp only [d, g', Equiv.optionSubtypeNe_none, Equiv.optionSubtypeNe_some,
      Endomorphism.DegreeUniqueness.withIdentity, Option.elim_none, Option.elim_some, hj₀]
  have h₁ := value_reindex A L f e i₀ hi₀ (fun i => a (e i))
  have h₂ := value_reindex A L g d j₀ hj₀ (fun j => b (d j))
  have h₃ := value_reindex A L (fun t : ι × κ => f t.1 * g t.2) (e.prodCongr d)
    (i₀, j₀) (by rw [hi₀, hj₀, one_mul]) (fun t => a (e t.1) * b (d t.2))
  simp only [hf, hg, Equiv.apply_symm_apply] at h₁ h₂
  simp only [Equiv.prodCongr_apply, Equiv.prodCongr_symm, Prod.map_fst, Prod.map_snd,
    Equiv.apply_symm_apply, hf, hg] at h₃
  rw [← h₃]
  exact (value_mul_withIdentity A L f' g' (fun i => a (e i)) (fun j => b (d j))).trans
    (congrArg₂ (fun x y : L => x * y) h₁ h₂)

end

/-! Collecting repeated endomorphism coordinates preserves the
scalar-extended geometric degree polynomial. -/

variable {K : Type} [Field K] [IsAlgClosed K]
  (A : Over (Spec (CommRingCat.of K))) [GrpObj A] [IsCommMonObj A]
  [IsProper A.hom] [Smooth A.hom] [GeometricallyIntegral A.hom]
  (L : Type*) [CommRing L] [Algebra ℚ L]

theorem value_pushforward {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (g : κ → AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd A) (e : ι → κ) (i₀ : ι) (hi₀ : g (e i₀) = 1) (x : ι → L) :
    value A L (fun i => g (e i)) x =
      value A L g (fun j => ∑ i, if j = e i then x i else 0) := by
  classical
  let M : κ → ι → ℕ := fun j i => if j = e i then 1 else 0
  have hM (i) : g (e i) = ∑ j, M j i • g j := by simp [M]
  have h := value_coordinates A L g (fun i => g (e i)) M hM i₀ hi₀ x
  simpa only [M, Nat.cast_ite, Nat.cast_one, Nat.cast_zero, ite_mul, one_mul, zero_mul] using h.symm

end NumberTheory.PadicHodge.IntegralComparison.DegreeNatural.LawScalarExtension

end

end OAI
