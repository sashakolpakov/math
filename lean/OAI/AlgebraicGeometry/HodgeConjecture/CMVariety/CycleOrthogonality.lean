import OAI.AlgebraicGeometry.HodgeConjecture.CMVariety.ProjectivePairing
import OAI.AlgebraicGeometry.HodgeConjecture.CMVariety.Decomposition
import OAI.AlgebraicGeometry.HodgeConjecture.CMVariety.CupPurity

/-! # Cycle Orthogonality -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMVariety.CycleOrthogonality.CM.Abelian

noncomputable section

/-! Diagonal and off-diagonal classes pair to zero in complementary degrees. -/

open _root_.CategoryTheory

theorem projectivePairing_cast_right (X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (k : ℕ)
    {l n : ℕ} (h : l = n)
    (hl : k + l = 2 * X.complexDimension) (hn : k + n = 2 * X.complexDimension)
    (a : X.complexCohomology k) (b : X.complexCohomology l) :
    ProjectivePairing.CM.Abelian.projectiveComplexPairing X k n hn a
      (cast (congrArg (fun d => (X.complexCohomology d : Type)) h) b) =
        ProjectivePairing.CM.Abelian.projectiveComplexPairing X k l hl a b := by
  subst n
  rfl

theorem projectivePairing_cast_left (X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (l : ℕ)
    {k n : ℕ} (h : k = n)
    (hk : k + l = 2 * X.complexDimension) (hn : n + l = 2 * X.complexDimension)
    (a : X.complexCohomology k) (b : X.complexCohomology l) :
    ProjectivePairing.CM.Abelian.projectiveComplexPairing X n l hn
      (cast (congrArg (fun d => (X.complexCohomology d : Type)) h) a) b =
        ProjectivePairing.CM.Abelian.projectiveComplexPairing X k l hk a b := by
  subst n
  rfl

theorem projectivePairing_zero_of_pure (X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (p q r s : ℕ)
    (hdim : (p + q) + (r + s) = 2 * X.complexDimension) (hneq : p + r ≠ q + s)
    (a : X.complexCohomology (p + q)) (b : X.complexCohomology (r + s))
    (ha : a ∈ X.pureBettiSubspace p q) (hb : b ∈ X.pureBettiSubspace r s) :
    ProjectivePairing.CM.Abelian.projectiveComplexPairing X (p + q) (r + s) hdim a b = 0 := by
  change ComplexMultiplication.CohomologyBaseChange.CM.evaluateComplexOnRationalHomology (TopCat.of X.analyticSpace) ((p + q) + (r + s))
    (AlgebraicTopology.Products.CupCohomology.singularCohomologyCup (R := ℂ) (Betti.Scheme.schemePointSpace X.toOver) (p + q) (r + s) a b) _ = 0
  rw [CupPurity.CM.Abelian.pure_top_cup_eq_zero X p q r s hdim hneq a b ha hb]
  exact LinearMap.congr_fun
    (map_zero (ComplexMultiplication.CohomologyBaseChange.CM.evaluateComplexOnRationalHomology (TopCat.of X.analyticSpace)
      ((p + q) + (r + s)))) _

theorem projectivePairing_diagonal_offDiagonal (X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (p q : ℕ)
    (hdim : (p + p) + (q + q) = 2 * X.complexDimension)
    (a : X.complexCohomology (p + p)) (ha : a ∈ X.pureBettiSubspace p p)
    (b : X.complexCohomology (q + q)) (hb : b ∈ Decomposition.CM.Abelian.offDiagonalBettiSubspace X q) :
    ProjectivePairing.CM.Abelian.projectiveComplexPairing X (p + p) (q + q) hdim a b = 0 := by
  apply Decomposition.CM.Abelian.linearMap_eq_zero_on_offDiagonal X q
    (ProjectivePairing.CM.Abelian.projectiveComplexPairing X (p + p) (q + q) hdim a) ?_ b hb
  intro i hi v hv
  have hn := (Decomposition.CM.Abelian.bidegree_ne_diagonal_iff q i).mp hi
  have hd := i.property
  have hdim' : (p + p) + (i.val.1 + i.val.2) = 2 * X.complexDimension := by omega
  have hz := projectivePairing_zero_of_pure X p p i.val.1 i.val.2 hdim' (by omega)
    a _ ha ((Decomposition.CM.Abelian.hodgePiece_mem_iff_native X (q + q) i v).mp hv)
  exact (projectivePairing_cast_right X (p + p) i.property.symm hdim hdim' a v).symm.trans hz

theorem projectivePairing_offDiagonal_diagonal (X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (p q : ℕ)
    (hdim : (p + p) + (q + q) = 2 * X.complexDimension)
    (a : X.complexCohomology (p + p)) (ha : a ∈ Decomposition.CM.Abelian.offDiagonalBettiSubspace X p)
    (b : X.complexCohomology (q + q)) (hb : b ∈ X.pureBettiSubspace q q) :
    ProjectivePairing.CM.Abelian.projectiveComplexPairing X (p + p) (q + q) hdim a b = 0 := by
  apply Decomposition.CM.Abelian.linearMap_eq_zero_on_offDiagonal X p
    ((ProjectivePairing.CM.Abelian.projectiveComplexPairing X (p + p) (q + q) hdim).flip b) ?_ a ha
  intro i hi v hv
  have hn := (Decomposition.CM.Abelian.bidegree_ne_diagonal_iff p i).mp hi
  have hd := i.property
  have hdim' : (i.val.1 + i.val.2) + (q + q) = 2 * X.complexDimension := by omega
  have hz := projectivePairing_zero_of_pure X i.val.1 i.val.2 q q hdim' (by omega)
    _ b ((Decomposition.CM.Abelian.hodgePiece_mem_iff_native X (p + p) i v).mp hv) hb
  exact (projectivePairing_cast_left X (q + q) i.property.symm hdim hdim' v b).symm.trans hz

theorem complexBettiPullback_cast {R X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety}
    (f : R.toOver ⟶ X.toOver) {m n : ℕ} (h : m = n) (a : X.complexCohomology m) :
    Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.complexBettiPullback f n
      (cast (congrArg (fun d => (X.complexCohomology d : Type)) h) a) =
    cast (congrArg (fun d => (R.complexCohomology d : Type)) h)
      (Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.complexBettiPullback f m a) := by
  subst n
  rfl

theorem pullback_offDiagonal_top_eq_zero {R X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety}
    (f : R.toOver ⟶ X.toOver) (q : ℕ) (htop : q + q = 2 * R.complexDimension)
    (a : X.complexCohomology (q + q)) (ha : a ∈ Decomposition.CM.Abelian.offDiagonalBettiSubspace X q) :
    Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.complexBettiPullback f (q + q) a = 0 := by
  apply Decomposition.CM.Abelian.linearMap_eq_zero_on_offDiagonal X q
    (Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.complexBettiPullback f (q + q)).hom ?_ a ha
  intro i hi v hv
  have hn := (Decomposition.CM.Abelian.bidegree_ne_diagonal_iff q i).mp hi
  have hd := i.property
  have hz := CycleForms.CM.Abelian.algebraicPullback_eq_zero_of_offDiagonal_top f i.val.1 i.val.2
    (by omega) hn _ ((Decomposition.CM.Abelian.hodgePiece_mem_iff_native X (q + q) i v).mp hv)
  rw [complexBettiPullback_cast f i.property.symm v] at hz
  exact (CupPurity.CM.Abelian.complexCohomology_cast_eq_zero_iff R i.property.symm _).mp hz

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMVariety.CycleOrthogonality.CM.Abelian
