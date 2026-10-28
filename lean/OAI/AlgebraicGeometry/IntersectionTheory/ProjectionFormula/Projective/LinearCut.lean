import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projective.AffineNeighborhood
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Supports

/-! # Linear Cut -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projective.LinearCut

noncomputable section

/-! Successive homogeneous linear forms cut every remaining component
properly. On a smooth m-dimensional projective presentation, m+1 such
forms therefore have no common zero. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped Classical

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Supports

def zeroSet {X : Scheme} {n : ℕ} (i : X ⟶ Foundations.Scheme.ProjectiveSpace.projectiveSpace n) (p : Foundations.Scheme.ProjectiveSpace.homogeneousCoordinateRing n) : Closeds X :=
  ⟨(i ⁻¹ᵁ Proj.basicOpen (Foundations.Scheme.ProjectiveSpace.projectiveGrading n) p : Set X)ᶜ,
    (i ⁻¹ᵁ Proj.basicOpen (Foundations.Scheme.ProjectiveSpace.projectiveGrading n) p).isOpen.isClosed_compl⟩

def commonZero {X : Scheme} {n k : ℕ} (i : X ⟶ Foundations.Scheme.ProjectiveSpace.projectiveSpace n)
    (L : Fin k → Foundations.Scheme.ProjectiveSpace.homogeneousCoordinateRing n) : Closeds X := ⨅ j, zeroSet i (L j)

theorem mem_commonZero {X : Scheme} {n k : ℕ} (i : X ⟶ Foundations.Scheme.ProjectiveSpace.projectiveSpace n)
    (L : Fin k → Foundations.Scheme.ProjectiveSpace.homogeneousCoordinateRing n) (x : X) :
    x ∈ commonZero i L ↔ ∀ j, L j ∈ (i x).asHomogeneousIdeal := by
  simp [commonZero, zeroSet, Proj.mem_basicOpen]

theorem exists_forms (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m k : ℕ)
    [SmoothOfRelativeDimension m X.structureMap] :
    ∃ L : Fin k → Foundations.Scheme.ProjectiveSpace.homogeneousCoordinateRing X.ambientDimension,
      (∀ j, L j ∈ Foundations.Scheme.ProjectiveSpace.projectiveGrading X.ambientDimension 1) ∧
      ∀ W : IrreducibleCloseds X.carrier,
        (W : Set X.carrier) ⊆ commonZero X.embedding L → k ≤ X.supportCodimension W := by
  induction k with
  | zero =>
    exact ⟨Fin.elim0, fun j => Fin.elim0 j, fun _ _ => Nat.zero_le _⟩
  | succ k ih =>
    obtain ⟨L, hL, hcodim⟩ := ih
    let S := commonZero X.embedding L
    let : NoetherianSpace S := NoetherianSpace.set (S : Set X.carrier)
    let : Finite (irreducibleComponents S) :=
      (NoetherianSpace.finite_irreducibleComponents (α := S)).to_subtype
    obtain ⟨p, hp, hav⟩ := AffineNeighborhood.exists_linear_form X.ambientDimension
      (fun D : irreducibleComponents S => X.embedding (CycleClass.Thom.IntersectionGeometry.supportPoint (CycleClass.Thom.IntersectionGeometry.closedComponentSupport X.carrier S D)))
    refine ⟨Fin.cons p L, ?_, ?_⟩
    · intro j
      refine Fin.cases hp (fun j => hL j) j
    · intro W hW
      have hWS : (W : Set X.carrier) ⊆ S := by
        intro x hx
        apply (mem_commonZero X.embedding L x).mpr
        intro j
        exact (mem_commonZero X.embedding (Fin.cons p L) x).mp (hW hx) j.succ
      obtain ⟨D, hD⟩ := Supports.closedComponentSupport_covers X.carrier S W hWS
      have hne : W ≠ CycleClass.Thom.IntersectionGeometry.closedComponentSupport X.carrier S D := by
        intro he
        have hx : CycleClass.Thom.IntersectionGeometry.supportPoint (CycleClass.Thom.IntersectionGeometry.closedComponentSupport X.carrier S D) ∈ (W : Set X.carrier) :=
          he ▸ (W.isIrreducible.isGenericPoint_genericPoint W.isClosed).mem
        exact hav D ((mem_commonZero X.embedding (Fin.cons p L) _).mp (hW hx) 0)
      have hlt := Supports.codimension_strictAnti X m (lt_of_le_of_ne hD hne)
      have hb := hcodim (CycleClass.Thom.IntersectionGeometry.closedComponentSupport X.carrier S D) (Supports.closedComponentSupport_subset X.carrier S D)
      omega

theorem exists_no_common_zero (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m : ℕ)
    [SmoothOfRelativeDimension m X.structureMap] :
    ∃ L : Fin (m + 1) → Foundations.Scheme.ProjectiveSpace.homogeneousCoordinateRing X.ambientDimension,
      (∀ j, L j ∈ Foundations.Scheme.ProjectiveSpace.projectiveGrading X.ambientDimension 1) ∧
      ∀ x : X.carrier, ∃ j, L j ∉ (X.embedding x).asHomogeneousIdeal := by
  obtain ⟨L, hL, hcodim⟩ := exists_forms X m (m + 1)
  refine ⟨L, hL, fun x => ?_⟩
  by_contra hn
  push Not at hn
  let W : IrreducibleCloseds X.carrier := irreducibleSetEquivPoints.symm x
  have hp : CycleClass.Thom.IntersectionGeometry.supportPoint W = x := irreducibleSetEquivPoints.apply_symm_apply x
  have hW : (W : Set X.carrier) ⊆ commonZero X.embedding L := by
    apply (Supports.supportPoint_mem_iff_subset (commonZero X.embedding L) W).mp
    rw [hp]
    exact (mem_commonZero X.embedding L x).mpr hn
  have hl := hcodim W hW
  have hd := Grading.supportDimension_add_codimension X m W
  omega

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projective.LinearCut
