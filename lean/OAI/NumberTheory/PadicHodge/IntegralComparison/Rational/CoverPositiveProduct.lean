import OAI.NumberTheory.PadicHodge.IntegralComparison.RationalDeRham.CoverProductEquiv
import OAI.NumberTheory.PadicHodge.IntegralComparison.GradedPositiveProduct

/-! # Cover Positive Product -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Rational.CoverPositiveProduct

noncomputable section

/-! Nonzero positive-degree products transfer between actual affine covers. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable (R : Type) [CommRing R] [Algebra ℚ R]
  (X : Over (Spec (CommRingCat.of R))) [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated]
  {ι κ : Type} (U : ι → X.left.Opens) (V : κ → X.left.Opens)
  (hU : iSup U = ⊤) (hV : iSup V = ⊤)
  (haU : ∀ i, IsAffineOpen (U i)) (haV : ∀ i, IsAffineOpen (V i))

local notation "H" => OAI.NumberTheory.PadicHodge.IntegralComparison.RationalDeRham.CoverProductEquiv.H R X
local notation "μ" => OAI.NumberTheory.PadicHodge.IntegralComparison.IntegralDeRham.CechProduct.cohomologyCup R X (OAI.NumberTheory.PadicHodge.IntegralComparison.NonemptyCechNerve.nerve U)
local notation "ν" => OAI.NumberTheory.PadicHodge.IntegralComparison.IntegralDeRham.CechProduct.cohomologyCup R X (OAI.NumberTheory.PadicHodge.IntegralComparison.NonemptyCechNerve.nerve V)

include hU hV haU haV in
theorem exists_nonzero (n : ℕ)
    (hn : ∃ v : Fin (n+1) → RationalDeRham.CoverProductEquiv.H R X U 1,
      GradedPositiveProduct.product (fun i j x y => μ i j x y) n v ≠ 0) :
    ∃ v : Fin (n+1) → RationalDeRham.CoverProductEquiv.H R X V 1,
      GradedPositiveProduct.product (fun i j x y => ν i j x y) n v ≠ 0 := by
  let e := RationalDeRham.CoverProductEquiv.equiv R X U V hU hV haU haV
  obtain ⟨v, hv⟩ := hn
  refine ⟨fun i => e 1 (v i), ?_⟩
  intro hz
  apply hv
  apply (e (n+1)).injective
  have he := GradedPositiveProduct.natural
    (fun i j x y => μ i j x y) (fun i j x y => ν i j x y) (fun i => e i)
    (RationalDeRham.CoverProductEquiv.equiv_cup R X U V hU hV haU haV) n v
  exact he.trans (hz.trans (map_zero _).symm)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Rational.CoverPositiveProduct
