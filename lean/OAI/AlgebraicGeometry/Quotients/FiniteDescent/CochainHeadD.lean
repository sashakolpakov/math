import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-! # Cochain Head D -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.CochainHeadD

noncomputable section

/-! Removing and adjoining the first term of a cochain complex. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v

namespace Construction.CochainHead

variable {V : Type u} [Category.{v} V] [HasZeroMorphisms V]

abbrev tail (C : CochainComplex V ℕ) : CochainComplex V ℕ :=
  CochainComplex.of (fun n => C.X (n + 1))
    (fun n => C.d (n + 1) (n + 1 + 1)) (fun _ => C.d_comp_d _ _ _)

theorem tail_d (C : CochainComplex V ℕ) (i j : ℕ) :
    (tail C).d i j = C.d (i + 1) (j + 1) := by
  by_cases h : i + 1 = j
  · subst j
    exact CochainComplex.of_d (fun n => C.X (n + 1))
      (fun n => C.d (n + 1) (n + 1 + 1)) i
  · rw [HomologicalComplex.shape _ _ _ h]
    exact (C.shape _ _ (by simpa only [ComplexShape.up_Rel, Nat.add_right_cancel_iff] using h)).symm

def tailMap {C D : CochainComplex V ℕ} (φ : C ⟶ D) : tail C ⟶ tail D :=
  CochainComplex.ofHom (fun i => φ.f (i + 1)) (by
    intro i
    rw [tail_d, tail_d]
    exact φ.comm _ _)

abbrev consX (A : V) (C : CochainComplex V ℕ) : ℕ → V
  | 0 => A
  | n + 1 => C.X n

abbrev consD (A : V) (C : CochainComplex V ℕ) (d : A ⟶ C.X 0) :
    ∀ n, consX A C n ⟶ consX A C (n + 1)
  | 0 => d
  | n + 1 => C.d n (n + 1)

abbrev cons (A : V) (C : CochainComplex V ℕ) (d : A ⟶ C.X 0)
    (h : d ≫ C.d 0 1 = 0) : CochainComplex V ℕ :=
  CochainComplex.of (consX A C) (consD A C d) (fun n => by
    cases n with
    | zero => exact h
    | succ n => exact C.d_comp_d _ _ _)

theorem cons_d_zero (A : V) (C : CochainComplex V ℕ) (d : A ⟶ C.X 0)
    (h : d ≫ C.d 0 1 = 0) : (cons A C d h).d 0 1 = d :=
  CochainComplex.of_d (consX A C) (consD A C d) 0

theorem cons_d_succ (A : V) (C : CochainComplex V ℕ) (d : A ⟶ C.X 0)
    (h : d ≫ C.d 0 1 = 0) (i j : ℕ) :
    (cons A C d h).d (i + 1) (j + 1) = C.d i j := by
  by_cases hij : i + 1 = j
  · subst j
    exact CochainComplex.of_d (consX A C) (consD A C d) (i + 1)
  · rw [HomologicalComplex.shape _ _ _ (by
      simpa only [ComplexShape.up_Rel, Nat.add_right_cancel_iff] using hij)]
    exact (C.shape _ _ hij).symm

def consMap {A B : V} {C D : CochainComplex V ℕ} (f : A ⟶ B) (φ : C ⟶ D)
    (d : A ⟶ C.X 0) (e : B ⟶ D.X 0)
    (hd : d ≫ C.d 0 1 = 0) (he : e ≫ D.d 0 1 = 0)
    (h : f ≫ e = d ≫ φ.f 0) : cons A C d hd ⟶ cons B D e he :=
  CochainComplex.ofHom (fun n => match n with
    | 0 => f
    | n + 1 => φ.f n) (by
      intro n
      cases n with
      | zero =>
          change f ≫ (cons B D e he).d 0 1 = (cons A C d hd).d 0 1 ≫ φ.f 0
          rw [cons_d_zero, cons_d_zero]
          exact h
      | succ n => simpa only [cons, CochainComplex.of_d, consD] using φ.comm n (n + 1))

def consTailIso (C : CochainComplex V ℕ) :
    cons (C.X 0) (tail C) (C.d 0 1) (by rw [tail_d]; exact C.d_comp_d _ _ _) ≅ C :=
  HomologicalComplex.Hom.isoOfComponents (fun n => match n with
    | 0 => Iso.refl _
    | _ + 1 => Iso.refl _) (by
      intro i j hij
      change i + 1 = j at hij
      subst j
      cases i <;> simp [cons, consD, tail, CochainComplex.of.d])

def tailWindowIso (C : CochainComplex V ℕ) (i j k : ℕ) :
    (tail C).sc' i j k ≅ C.sc' (i + 1) (j + 1) (k + 1) :=
  ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by
      change 𝟙 (C.X (i + 1)) ≫ C.d (i + 1) (j + 1) =
        (tail C).d i j ≫ 𝟙 (C.X (j + 1))
      rw [Category.id_comp, Category.comp_id, tail_d])
    (by
      change 𝟙 (C.X (j + 1)) ≫ C.d (j + 1) (k + 1) =
        (tail C).d j k ≫ 𝟙 (C.X (k + 1))
      rw [Category.id_comp, Category.comp_id, tail_d])

end Construction.CochainHead

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.CochainHeadD
