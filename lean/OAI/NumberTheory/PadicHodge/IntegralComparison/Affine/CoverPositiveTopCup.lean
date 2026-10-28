import OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.PositiveTopCup
import OAI.NumberTheory.PadicHodge.IntegralComparison.RationalDeRham.CoverProductEquiv

/-! # Cover Positive Top Cup -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.CoverPositiveTopCup

noncomputable section

/-! Every actual affine cover of a complex abelian variety has a
nonzero top product of degree-one classes in its original Čech total. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
local instance smooth : Smooth A.toOver.hom := A.variety.presentation.smooth
local instance proper : IsProper A.toOver.hom := A.variety.presentation.projective.isProper
local instance separated : A.toOver.left.IsSeparated := by
  constructor
  rw [← terminal.comp_from A.toOver.hom]
  infer_instance

variable {ι : Type} (U : ι → A.toOver.left.Opens)
  (hU : iSup U = ⊤) (haU : ∀ i, IsAffineOpen (U i))

abbrev H (q : ℕ) :=
  (IntegralDeRham.CechProduct.total ℂ A.toOver (NonemptyCechNerve.nerve U)).homology q

abbrev cup (p q : ℕ) (x : H A U p) (y : H A U q) :=
  IntegralDeRham.CechProduct.cohomologyCup ℂ A.toOver (NonemptyCechNerve.nerve U) p q x y

def comparison (q : ℕ) : H A U q ≃ₗ[ℂ] Projective.DeRhamTopCup.H A.variety q :=
  RationalDeRham.CoverProductEquiv.equiv ℂ A.toOver U
    (Projective.CechBettiEquivalence.cover A.variety)
    hU (Projective.CechBettiEquivalence.cover_covers A.variety)
    haU (Projective.CechBettiEquivalence.cover_affine A.variety) q

theorem comparison_cup (p q : ℕ) (x : H A U p) (y : H A U q) :
    comparison A U hU haU (p+q) (cup A U p q x y) =
      Projective.PositiveTopCup.cup A.variety p q
        (comparison A U hU haU p x) (comparison A U hU haU q y) :=
  RationalDeRham.CoverProductEquiv.equiv_cup ℂ A.toOver U
    (Projective.CechBettiEquivalence.cover A.variety)
    hU (Projective.CechBettiEquivalence.cover_covers A.variety)
    haU (Projective.CechBettiEquivalence.cover_affine A.variety) p q x y

include hU haU in
theorem exists_nonzero (n : ℕ) (hn : n+1 = 2*A.variety.complexDimension) :
    ∃ v : Fin (n+1) → H A U 1,
      GradedPositiveProduct.product (cup A U) n v ≠ 0 := by
  obtain ⟨v, hv⟩ := Projective.PositiveTopCup.exists_nonzero A n hn
  let w := fun i => (comparison A U hU haU 1).symm (v i)
  refine ⟨w, ?_⟩
  intro hz
  have he := GradedPositiveProduct.natural (cup A U)
    (Projective.PositiveTopCup.cup A.variety)
    (fun q => comparison A U hU haU q) (comparison_cup A U hU haU) n w
  apply hv
  simpa only [w, LinearEquiv.apply_symm_apply, hz, map_zero] using he.symm

include hU haU in
theorem positive_dimension (hpos : 0 < A.variety.complexDimension) :
    ∃ v : Fin ((2*A.variety.complexDimension-1)+1) → H A U 1,
      GradedPositiveProduct.product (cup A U) (2*A.variety.complexDimension-1) v ≠ 0 :=
  exists_nonzero A U hU haU _ (by omega)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.CoverPositiveTopCup
