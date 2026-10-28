import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Finite.PolynomialCoverExpansion
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Finite.CoverCombinatorics

/-! # Common Cover -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Finite.CommonCover.ProjectiveCech

noncomputable section

/-! Two finite homogeneous linear covers with the same coefficient-linear span have equivalent graded Čech exactness. -/

open _root_.MvPolynomial DirectSum

universe u v w

variable {τ : Type u} [Fintype τ] (R : Type v) [CommRing R]
variable (M : Type w) [AddCommGroup M] [Module R M] [Module (MvPolynomial τ R) M]
  [IsScalarTower R (MvPolynomial τ R) M]
variable (ℳ : ℤ → Submodule R M) [Decomposition ℳ]
  [SetLike.GradedSMul (WeightedFreeModules.GradedModules.polynomialIntegerGrading (σ := τ) R) ℳ]

theorem polynomialCover_concat_left_exact_iff {n m : ℕ}
    (a : Fin n → MvPolynomial τ R) (b : Fin m → MvPolynomial τ R)
    (ha : ∀ i, (a i).IsHomogeneous 1) (hb : ∀ i, (b i).IsHomogeneous 1)
    (hspan : ∀ i, b i ∈ Submodule.span R (Set.range a)) (d : ℤ) (q : ℕ) :
    Polynomial.CoverModule.ProjectiveCech.polynomialCoverCechExactAt R (MvPolynomial τ R) M (Fin.append a b) ℳ d q ↔
      Polynomial.CoverModule.ProjectiveCech.polynomialCoverCechExactAt R (MvPolynomial τ R) M a ℳ d q := by
  induction m with
  | zero =>
    rw [Fin.append_right_nil a b rfl]
    exact CoverCombinatorics.ProjectiveCech.polynomialCover_cast_exact_iff R (MvPolynomial τ R) M _ a ℳ d q
  | succ m ih =>
    have ht : ∀ i, (Fin.init b i).IsHomogeneous 1 := fun i => hb i.castSucc
    have hs : ∀ i, Fin.init b i ∈ Submodule.span R (Set.range a) := fun i => hspan i.castSucc
    have hab : ∀ i, (Fin.append a (Fin.init b) i).IsHomogeneous 1 := by
      intro i
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · simpa only [Fin.append_left] using ha j
      · simpa only [Fin.append_right] using ht j
    have hx : b (Fin.last m) ∈ Submodule.span R (Set.range (Fin.append a (Fin.init b))) :=
      CoverCombinatorics.ProjectiveCech.cover_span_le_append_left R a (Fin.init b) (hspan (Fin.last m))
    have heq : Fin.append a b = Fin.snoc (Fin.append a (Fin.init b)) (b (Fin.last m)) := by
      rw [← Fin.append_snoc, Fin.snoc_init_self]
    rw [heq]
    exact (PolynomialCoverExpansion.ProjectiveCech.polynomialCover_snoc_span_exact_iff R M ℳ _ hab _ hx d q).trans
      (ih (Fin.init b) ht hs)

theorem polynomialCover_concat_right_exact_iff {n m : ℕ}
    (a : Fin n → MvPolynomial τ R) (b : Fin m → MvPolynomial τ R)
    (ha : ∀ i, (a i).IsHomogeneous 1) (hb : ∀ i, (b i).IsHomogeneous 1)
    (hspan : ∀ i, a i ∈ Submodule.span R (Set.range b)) (d : ℤ) (q : ℕ) :
    Polynomial.CoverModule.ProjectiveCech.polynomialCoverCechExactAt R (MvPolynomial τ R) M (Fin.append a b) ℳ d q ↔
      Polynomial.CoverModule.ProjectiveCech.polynomialCoverCechExactAt R (MvPolynomial τ R) M b ℳ d q := by
  induction n with
  | zero =>
    rw [Fin.append_left_nil a b rfl]
    exact CoverCombinatorics.ProjectiveCech.polynomialCover_cast_exact_iff R (MvPolynomial τ R) M _ b ℳ d q
  | succ n ih =>
    have ht : ∀ i, (Fin.tail a i).IsHomogeneous 1 := fun i => ha i.succ
    have hs : ∀ i, Fin.tail a i ∈ Submodule.span R (Set.range b) := fun i => hspan i.succ
    have hab : ∀ i, (Fin.append (Fin.tail a) b i).IsHomogeneous 1 := by
      intro i
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · simpa only [Fin.append_left] using ht j
      · simpa only [Fin.append_right] using hb j
    have hx : a 0 ∈ Submodule.span R (Set.range (Fin.append (Fin.tail a) b)) :=
      CoverCombinatorics.ProjectiveCech.cover_span_le_append_right R (Fin.tail a) b (hspan 0)
    have heq : Fin.append a b = Fin.cons (a 0) (Fin.append (Fin.tail a) b) ∘
        Fin.cast (Nat.add_right_comm n 1 m) := by
      rw [← Fin.append_cons, Fin.cons_self_tail]
    rw [heq]
    exact (CoverCombinatorics.ProjectiveCech.polynomialCover_cast_exact_iff R (MvPolynomial τ R) M _ _ ℳ d q).trans
      ((PolynomialCoverExpansion.ProjectiveCech.polynomialCover_cons_span_exact_iff R M ℳ _ hab _ hx d q).trans
        (ih (Fin.tail a) ht hs))

theorem polynomialCover_exact_iff_of_span_eq {n m : ℕ}
    (a : Fin n → MvPolynomial τ R) (b : Fin m → MvPolynomial τ R)
    (ha : ∀ i, (a i).IsHomogeneous 1) (hb : ∀ i, (b i).IsHomogeneous 1)
    (hspan : Submodule.span R (Set.range a) = Submodule.span R (Set.range b)) (d : ℤ) (q : ℕ) :
    Polynomial.CoverModule.ProjectiveCech.polynomialCoverCechExactAt R (MvPolynomial τ R) M a ℳ d q ↔
      Polynomial.CoverModule.ProjectiveCech.polynomialCoverCechExactAt R (MvPolynomial τ R) M b ℳ d q := by
  have hba (i) : b i ∈ Submodule.span R (Set.range a) := by
    rw [hspan]
    exact Submodule.subset_span (Set.mem_range_self i)
  have hab (i) : a i ∈ Submodule.span R (Set.range b) := by
    rw [← hspan]
    exact Submodule.subset_span (Set.mem_range_self i)
  exact (polynomialCover_concat_left_exact_iff R M ℳ a b ha hb hba d q).symm.trans
    (polynomialCover_concat_right_exact_iff R M ℳ a b ha hb hab d q)

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Finite.CommonCover.ProjectiveCech
