/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project
This file has been modified.
-/
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coordinate.SectionCover
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.AffineOpen.SectionExtension

/-! # Chart Section Extension -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coordinate

noncomputable section

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u v

variable {X : Scheme.{u}} {ι : Type v} (D : SectionCover.CoordinateSectionCover X ι)

lemma SectionCover.CoordinateSectionCover.exists_coordinateChartExtension
    (M : X.Modules) [M.IsQuasicoherent]
    (i j : ι) (s : Γ(M, D.opens j)) :
    ∃ (n : ℕ) (t : Γ(M, D.opens i)),
      M.presheaf.map
          (homOfLE (D.overlap_le_left i j)).op t =
        X.presheaf.map
              (homOfLE (D.overlap_le_left i j)).op
              (D.ratio i j ^ n) •
          M.presheaf.map
            (homOfLE (D.overlap_le_right i j)).op s := by
  let X := X
  let U : X.affineOpens :=
    ⟨D.opens i, D.affine i⟩
  let f := D.ratio i j
  have hV : X.basicOpen f = D.overlap i j :=
    D.basicOpen_ratio i j
  let e : Γ(M, D.overlap i j) ≅
      Γ(M, X.basicOpen f) :=
    M.presheaf.mapIso (eqToIso hV).op
  let r : Γ(M, X.basicOpen f) :=
    e.hom (M.presheaf.map
      (homOfLE (D.overlap_le_right i j)).op s)
  obtain ⟨n, t, ht⟩ :=
    AffineOpen.SectionExtension.affineOpen_quasicoherent_section_clear_denominator
      M U f r
  refine ⟨n, t, ?_⟩
  apply (ConcreteCategory.bijective_of_isIso e.hom).1
  have hleft :
      e.hom
          (M.presheaf.map
            (homOfLE (D.overlap_le_left i j)).op t) =
        M.presheaf.map (homOfLE (X.basicOpen_le f)).op t := by
    simp only [e, Functor.mapIso_hom, ← M.presheaf.map_comp_apply]
    exact ConcreteCategory.congr_hom
      (M.presheaf.congr_map (Subsingleton.elim _ _)) _
  have hright :
      e.hom
          (X.presheaf.map
                (homOfLE (D.overlap_le_left i j)).op
                (D.ratio i j ^ n) •
            M.presheaf.map
              (homOfLE (D.overlap_le_right i j)).op s) =
        X.presheaf.map (homOfLE (X.basicOpen_le f)).op (f ^ n) • r := by
    have hmap := M.val.map_smul (eqToIso hV).op.hom
      (X.presheaf.map
        (homOfLE (D.overlap_le_left i j)).op
        (D.ratio i j ^ n))
      (M.presheaf.map
        (homOfLE (D.overlap_le_right i j)).op s)
    refine hmap.trans ?_
    have hsection :
        M.val.map (eqToIso hV).op.hom
            (M.presheaf.map
              (homOfLE (D.overlap_le_right i j)).op s) =
          r := by
      rfl
    rw [hsection]
    apply congrArg (fun a : Γ(X, X.basicOpen f) ↦ a • r)
    change X.ringCatSheaf.obj.map (eqToIso hV).op.hom
        (X.ringCatSheaf.obj.map
          (homOfLE (D.overlap_le_left i j)).op
          (f ^ n)) =
      X.ringCatSheaf.obj.map (homOfLE (X.basicOpen_le f)).op (f ^ n)
    have hcomp :
        X.ringCatSheaf.obj.map
              (homOfLE (D.overlap_le_left i j)).op ≫
            X.ringCatSheaf.obj.map (eqToIso hV).op.hom =
          X.ringCatSheaf.obj.map (homOfLE (X.basicOpen_le f)).op := by
      rw [← Functor.map_comp]
      exact X.ringCatSheaf.obj.congr_map (Subsingleton.elim _ _)
    exact ConcreteCategory.congr_hom hcomp (f ^ n)
  exact hleft.trans (ht.trans hright.symm)

/-- Over a finite standard coordinate cover, the chart extensions of a section may all be
chosen with one common coordinate-ratio exponent. -/
lemma SectionCover.CoordinateSectionCover.exists_coordinateChartExtension_forall [Fintype ι]
    (M : X.Modules) [M.IsQuasicoherent]
    (j : ι) (s : Γ(M, D.opens j)) :
    ∃ (n : ℕ) (t : ∀ i : ι, Γ(M, D.opens i)), ∀ i,
      M.presheaf.map
          (homOfLE (D.overlap_le_left i j)).op (t i) =
        X.presheaf.map
              (homOfLE (D.overlap_le_left i j)).op
              (D.ratio i j ^ n) •
          M.presheaf.map
            (homOfLE (D.overlap_le_right i j)).op s := by
  classical
  choose n t ht using fun i ↦ SectionCover.CoordinateSectionCover.exists_coordinateChartExtension D M i j s
  let N := Finset.univ.sup n
  have hle (i : ι) : n i ≤ N := Finset.le_sup (Finset.mem_univ i)
  refine ⟨N, fun i ↦
    D.ratio i j ^ (N - n i) • t i,
    fun i ↦ ?_⟩
  rw [M.map_smul, ht i, ← mul_smul, ← map_mul, ← pow_add,
    Nat.sub_add_cancel (hle i)]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coordinate
