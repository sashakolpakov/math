import OAI.NumberTheory.PadicHodge.IntegralComparison.RationalDeRham.CoverRefinement
import OAI.NumberTheory.PadicHodge.IntegralComparison.IntegralDeRham.RationalProduct

/-! # Cover Product Equiv -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.RationalDeRham.CoverProductEquiv

noncomputable section

/-! Any two genuine affine covers have a product-preserving comparison
through their actual common intersection cover. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem transfer_cup {R : Type*} [CommRing R]
    {A B D : ℕ → Type*}
    [∀ n, AddCommGroup (A n)] [∀ n, Module R (A n)]
    [∀ n, AddCommGroup (B n)] [∀ n, Module R (B n)]
    [∀ n, AddCommGroup (D n)] [∀ n, Module R (D n)]
    (μ : ∀ i j, A i → A j → A (i+j))
    (ν : ∀ i j, B i → B j → B (i+j))
    (ρ : ∀ i j, D i → D j → D (i+j))
    (l : ∀ i, A i ≃ₗ[R] D i) (r : ∀ i, B i ≃ₗ[R] D i)
    (hl : ∀ i j x y, l (i+j) (μ i j x y) = ρ i j (l i x) (l j y))
    (hr : ∀ i j x y, r (i+j) (ν i j x y) = ρ i j (r i x) (r j y))
    (i j : ℕ) (x : A i) (y : A j) :
    ((l (i+j)).trans (r (i+j)).symm) (μ i j x y) =
      ν i j (((l i).trans (r i).symm) x) (((l j).trans (r j).symm) y) := by
  apply (r (i+j)).injective
  simp only [LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
  rw [hr]
  simp only [LinearEquiv.apply_symm_apply]
  exact hl i j x y

variable (R : Type) [CommRing R] [Algebra ℚ R]
  (X : Over (Spec (CommRingCat.of R))) [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated]
  {ι κ : Type} (U : ι → X.left.Opens) (V : κ → X.left.Opens)
  (hU : iSup U = ⊤) (hV : iSup V = ⊤)
  (haU : ∀ i, IsAffineOpen (U i)) (haV : ∀ i, IsAffineOpen (V i))

abbrev H {τ : Type} (W : τ → X.left.Opens) (n : ℕ) :=
  (IntegralDeRham.CechProduct.total R X (NonemptyCechNerve.nerve W)).homology n

theorem refinement_cup (r : FormalCoproduct.mk κ V ⟶ FormalCoproduct.mk ι U)
    (p q : ℕ) (x : H R X U p) (y : H R X U q) :
    (CoverRefinement.homologyIso R X U V r hU hV haU haV (p+q)).hom
      (IntegralDeRham.CechProduct.cohomologyCup R X (NonemptyCechNerve.nerve U) p q x y) =
    IntegralDeRham.CechProduct.cohomologyCup R X (NonemptyCechNerve.nerve V) p q
      ((CoverRefinement.homologyIso R X U V r hU hV haU haV p).hom x)
      ((CoverRefinement.homologyIso R X U V r hU hV haU haV q).hom y) :=
  Cech.RefinementTotalCup.homologyMap_cup U V r (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.presheafComplex R X)
    (IntegralDeRham.CechProduct.sectionPairing R X)
    (IntegralDeRham.CechProduct.sectionPairing_natural R X)
    (IntegralDeRham.CechProduct.sectionPairing_differential R X) p q x y

def common : ι × κ → X.left.Opens := fun a => U a.1 ⊓ V a.2

include hU hV in
omit [Algebra ℚ R] [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated] in
theorem common_covers : iSup (common R X U V) = ⊤ := by
  apply top_unique
  intro x _
  have hxU : x ∈ iSup U := by rw [hU]; trivial
  have hxV : x ∈ iSup V := by rw [hV]; trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hxU
  obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.mp hxV
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨(i,j), hi, hj⟩

include haU haV in
omit [Algebra ℚ R] [IsProper X.hom] [Smooth X.hom] in
theorem common_affine (a : ι × κ) : IsAffineOpen (common R X U V a) :=
  (haU a.1).inf (haV a.2)

def leftRefinement : FormalCoproduct.mk (ι × κ) (common R X U V) ⟶ FormalCoproduct.mk ι U where
  f := Prod.fst
  φ _ := homOfLE inf_le_left

def rightRefinement : FormalCoproduct.mk (ι × κ) (common R X U V) ⟶ FormalCoproduct.mk κ V where
  f := Prod.snd
  φ _ := homOfLE inf_le_right

def leftIso (n : ℕ) := CoverRefinement.homologyIso
  R X U (common R X U V) (leftRefinement R X U V)
  hU (common_covers R X U V hU hV) haU (common_affine R X U V haU haV) n

def rightIso (n : ℕ) := CoverRefinement.homologyIso
  R X V (common R X U V) (rightRefinement R X U V)
  hV (common_covers R X U V hU hV) haV (common_affine R X U V haU haV) n

def equiv (n : ℕ) : H R X U n ≃ₗ[R] H R X V n :=
  (leftIso R X U V hU hV haU haV n).toLinearEquiv.trans
    (rightIso R X U V hU hV haU haV n).toLinearEquiv.symm

theorem equiv_cup (p q : ℕ) (x : H R X U p) (y : H R X U q) :
    equiv R X U V hU hV haU haV (p+q)
      (IntegralDeRham.CechProduct.cohomologyCup R X (NonemptyCechNerve.nerve U) p q x y) =
    IntegralDeRham.CechProduct.cohomologyCup R X (NonemptyCechNerve.nerve V) p q
      (equiv R X U V hU hV haU haV p x) (equiv R X U V hU hV haU haV q y) :=
  transfer_cup
    (fun i j x y => IntegralDeRham.CechProduct.cohomologyCup R X
      (NonemptyCechNerve.nerve U) i j x y)
    (fun i j x y => IntegralDeRham.CechProduct.cohomologyCup R X
      (NonemptyCechNerve.nerve V) i j x y)
    (fun i j x y => IntegralDeRham.CechProduct.cohomologyCup R X
      (NonemptyCechNerve.nerve (common R X U V)) i j x y)
    (fun i => (leftIso R X U V hU hV haU haV i).toLinearEquiv)
    (fun i => (rightIso R X U V hU hV haU haV i).toLinearEquiv)
    (refinement_cup R X U (common R X U V) hU (common_covers R X U V hU hV)
      haU (common_affine R X U V haU haV) (leftRefinement R X U V))
    (refinement_cup R X V (common R X U V) hV (common_covers R X U V hU hV)
      haV (common_affine R X U V haU haV) (rightRefinement R X U V)) p q x y

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.RationalDeRham.CoverProductEquiv
