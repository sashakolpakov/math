/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project
This file has been modified.
-/
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coordinate.ChartSectionExtension
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.AffineOpen.SectionVanishing

/-! # Chart Difference -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coordinate

noncomputable section

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u v

variable {X : Scheme.{u}} {ι : Type v} (D : SectionCover.CoordinateSectionCover X ι)

lemma SectionCover.CoordinateSectionCover.exists_pow_coordinateChartDifference_eq_zero
    (M : X.Modules) [M.IsQuasicoherent]
    (i k j : ι) (n : ℕ)
    (s : Γ(M, D.opens j))
    (tI : Γ(M, D.opens i))
    (tK : Γ(M, D.opens k))
    (hI : M.presheaf.map
          (homOfLE (D.overlap_le_left i j)).op tI =
        X.presheaf.map
              (homOfLE (D.overlap_le_left i j)).op
              (D.ratio i j ^ n) •
          M.presheaf.map
            (homOfLE (D.overlap_le_right i j)).op s)
    (hK : M.presheaf.map
          (homOfLE (D.overlap_le_left k j)).op tK =
        X.presheaf.map
              (homOfLE (D.overlap_le_left k j)).op
              (D.ratio k j ^ n) •
          M.presheaf.map
            (homOfLE (D.overlap_le_right k j)).op s) :
    ∃ m : ℕ,
      (X.presheaf.map
          (homOfLE (D.overlap_le_left i k)).op
          (D.ratio i j)) ^ m •
        (M.presheaf.map
            (homOfLE (D.overlap_le_left i k)).op tI -
          (D.transition i k :
              Γ(X,
                D.overlap i k)) ^ n •
            M.presheaf.map
              (homOfLE (D.overlap_le_right i k)).op tK) = 0 := by
  let Xp := X
  let W := D.overlap i k
  let r : Γ(Xp, W) := Xp.presheaf.map
    (homOfLE (D.overlap_le_left i k)).op
    (D.ratio i j)
  let d : Γ(M, W) := M.presheaf.map
      (homOfLE (D.overlap_le_left i k)).op tI -
    (D.transition i k : Γ(Xp, W)) ^ n •
      M.presheaf.map
        (homOfLE (D.overlap_le_right i k)).op tK
  have hW : IsAffineOpen W := D.affine_overlap i k
  let U : Xp.affineOpens := ⟨W, hW⟩
  apply
    AffineOpen.SectionVanishing.affineOpen_quasicoherent_section_vanishing
      M U r d
  let V := Xp.basicOpen r
  have hV : V = W ⊓ D.opens j :=
    D.overlap_basicOpen_ratio i k j
  have hVI : V ≤ D.overlap i j := by
    rw [hV]
    dsimp only [W]
    rw [D.overlap_eq, D.overlap_eq]
    exact le_inf (inf_le_left.trans inf_le_left) inf_le_right
  have hVK : V ≤ D.overlap k j := by
    rw [hV]
    dsimp only [W]
    rw [D.overlap_eq, D.overlap_eq]
    exact le_inf (inf_le_left.trans inf_le_right) inf_le_right
  have hMcomp : ∀ {A B C : Xp.Opens} (hBA : B ≤ A) (hCB : C ≤ B)
      (x : Γ(M, A)),
      M.presheaf.map (homOfLE hCB).op
          (M.presheaf.map (homOfLE hBA).op x) =
        M.presheaf.map (homOfLE (hCB.trans hBA)).op x := by
    intro A B C hBA hCB x
    rw [← M.presheaf.map_comp_apply]
    exact ConcreteCategory.congr_hom
      (M.presheaf.congr_map (Subsingleton.elim _ _)) x
  have hXcomp : ∀ {A B C : Xp.Opens} (hBA : B ≤ A) (hCB : C ≤ B)
      (x : Γ(Xp, A)),
      Xp.presheaf.map (homOfLE hCB).op
          (Xp.presheaf.map (homOfLE hBA).op x) =
        Xp.presheaf.map (homOfLE (hCB.trans hBA)).op x := by
    intro A B C hBA hCB x
    rw [← Xp.presheaf.map_comp_apply]
    exact ConcreteCategory.congr_hom
      (Xp.presheaf.congr_map (Subsingleton.elim _ _)) x
  have hI' := congrArg (M.presheaf.map (homOfLE hVI).op) hI
  rw [M.map_smul, hMcomp, hXcomp, hMcomp] at hI'
  have hK' := congrArg (M.presheaf.map (homOfLE hVK).op) hK
  rw [M.map_smul, hMcomp, hXcomp, hMcomp] at hK'
  change M.presheaf.map (homOfLE (Xp.basicOpen_le r)).op d = 0
  dsimp only [d]
  rw [map_sub, M.map_smul, hMcomp, map_pow, hMcomp]
  rw [hI', hK']
  have hr := congrArg
    (Xp.presheaf.map (homOfLE (Xp.basicOpen_le r)).op)
    (D.ratio_transition i k j)
  dsimp only [Xp] at hXcomp hr ⊢
  simp only [map_mul, hXcomp] at hr
  rw [map_pow, map_pow]
  rw [hr, mul_pow, mul_smul]
  dsimp only [SectionCover.CoordinateSectionCover.transition]
  simp only [hXcomp, sub_self]

/-- Over a finite standard coordinate cover, all transition-adjusted differences between
common-degree chart extensions are annihilated by one common coordinate power. -/
lemma SectionCover.CoordinateSectionCover.exists_pow_coordinateChartDifference_eq_zero_forall [Fintype ι]
    (M : X.Modules) [M.IsQuasicoherent]
    (j : ι) (n : ℕ)
    (s : Γ(M, D.opens j))
    (t : ∀ i : ι, Γ(M, D.opens i))
    (ht : ∀ i,
      M.presheaf.map
          (homOfLE (D.overlap_le_left i j)).op (t i) =
        X.presheaf.map
              (homOfLE (D.overlap_le_left i j)).op
              (D.ratio i j ^ n) •
          M.presheaf.map
            (homOfLE (D.overlap_le_right i j)).op s) :
    ∃ m : ℕ, ∀ i k : ι,
      (X.presheaf.map
          (homOfLE (D.overlap_le_left i k)).op
          (D.ratio i j)) ^ m •
        (M.presheaf.map
            (homOfLE (D.overlap_le_left i k)).op (t i) -
          (D.transition i k :
              Γ(X,
                D.overlap i k)) ^ n •
            M.presheaf.map
              (homOfLE (D.overlap_le_right i k)).op (t k)) = 0 := by
  classical
  choose e he using fun p : ι × ι ↦
    SectionCover.CoordinateSectionCover.exists_pow_coordinateChartDifference_eq_zero
      D M p.1 p.2 j n s (t p.1) (t p.2) (ht p.1) (ht p.2)
  let m := Finset.univ.sup e
  refine ⟨m, fun i k ↦ ?_⟩
  have hle : e (i, k) ≤ m := Finset.le_sup (Finset.mem_univ (i, k))
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hle
  rw [hd, pow_add, mul_comm, mul_smul, he (i, k), smul_zero]

/-- Multiplying two chart extensions by the common annihilating coordinate power
turns their degree-`n` compatibility modulo torsion into exact degree-`n + m`
compatibility. -/
lemma SectionCover.CoordinateSectionCover.coordinateChartExtensions_corrected_compatible
    (M : X.Modules)
    (i k j : ι) (n m : ℕ)
    (tI : Γ(M, D.opens i))
    (tK : Γ(M, D.opens k))
    (h :
      (X.presheaf.map
          (homOfLE (D.overlap_le_left i k)).op
          (D.ratio i j)) ^ m •
        (M.presheaf.map
            (homOfLE (D.overlap_le_left i k)).op tI -
          (D.transition i k :
              Γ(X,
                D.overlap i k)) ^ n •
            M.presheaf.map
              (homOfLE (D.overlap_le_right i k)).op tK) = 0) :
    M.presheaf.map
        (homOfLE (D.overlap_le_left i k)).op
        (D.ratio i j ^ m • tI) =
      (D.transition i k :
          Γ(X,
            D.overlap i k)) ^ (n + m) •
        M.presheaf.map
          (homOfLE (D.overlap_le_right i k)).op
          (D.ratio k j ^ m • tK) := by
  let Xp := X
  let W := D.overlap i k
  let r : Γ(Xp, W) := Xp.presheaf.map
    (homOfLE (D.overlap_le_left i k)).op
    (D.ratio i j)
  let q : Γ(Xp, W) := Xp.presheaf.map
    (homOfLE (D.overlap_le_right i k)).op
    (D.ratio k j)
  let u : Γ(Xp, W) := D.transition i k
  let a : Γ(M, W) := M.presheaf.map
    (homOfLE (D.overlap_le_left i k)).op tI
  let b : Γ(M, W) := M.presheaf.map
    (homOfLE (D.overlap_le_right i k)).op tK
  have hr : r = u * q :=
    D.ratio_transition i k j
  have hab : r ^ m • a = r ^ m • (u ^ n • b) := by
    apply sub_eq_zero.mp
    rw [← smul_sub]
    exact h
  have hscalar : r ^ m * u ^ n = u ^ (n + m) * q ^ m := by
    rw [hr, mul_pow, pow_add]
    ring
  calc
    _ = r ^ m • a := by rw [M.map_smul, map_pow]
    _ = r ^ m • (u ^ n • b) := hab
    _ = (r ^ m * u ^ n) • b := by rw [mul_smul]
    _ = (u ^ (n + m) * q ^ m) • b := by rw [hscalar]
    _ = u ^ (n + m) • (q ^ m • b) := by rw [mul_smul]
    _ = _ := by rw [M.map_smul, map_pow]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coordinate
