import OAI.AlgebraicGeometry.Crystalline.Cohomology.NonemptyCechExtra

/-! # Fiber Tuple -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.FiberTuple.FiberTupleCech

noncomputable section

/-!
# Contraction of tuple nerves over a family of sets

A simplex is an ordered nonempty tuple in one fibre. Its augmentation
records the base point together with the fact that its fibre is inhabited.
Choosing a point in each inhabited fibre gives an extra degeneracy. Thus
coproduct coefficients give an exact chain complex in positive degrees,
including when some or all fibres are empty.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite Simplicial _root_.AlgebraicTopology

universe u v w

variable {α : Type u} (S : α → Type u)

def nerve : SimplicialObject (Type u) where
  obj n := Σ a : α, ToType n.unop → S a
  map f := ↾fun z => ⟨z.1, z.2 ∘ f.unop.toOrderHom⟩
  map_id _ := by apply ConcreteCategory.hom_ext; rintro ⟨a, f⟩; rfl
  map_comp _ _ := by apply ConcreteCategory.hom_ext; rintro ⟨a, f⟩; rfl

def augmented : SimplicialObject.Augmented (Type u) where
  left := nerve S
  right := {a : α // Nonempty (S a)}
  hom :=
    { app _ := ↾fun z => ⟨z.1, ⟨z.2 0⟩⟩
      naturality _ _ _ := by apply ConcreteCategory.hom_ext; rintro ⟨a, f⟩; rfl }

def extraDegeneracy : SimplicialObject.Augmented.ExtraDegeneracy (augmented S) where
  s' := ↾fun a => ⟨a.val, fun _ => Classical.choice a.property⟩
  s _ := ↾fun z => ⟨z.1, Fin.cons (Classical.choice (show Nonempty (S z.1) from ⟨z.2 0⟩)) z.2⟩
  s'_comp_ε := by apply ConcreteCategory.hom_ext; rintro ⟨a, ha⟩; rfl
  s₀_comp_δ₁ := by
    apply ConcreteCategory.hom_ext
    rintro ⟨a, f⟩
    change Fin 1 → S a at f
    change (⟨a, fun i : Fin 1 =>
      (Fin.cons (Classical.choice (show Nonempty (S a) from ⟨f 0⟩)) f : Fin 2 → S a)
        ((1 : Fin 2).succAbove i)⟩ : Σ a : α, Fin 1 → S a) =
      ⟨a, fun _ => Classical.choice (show Nonempty (S a) from ⟨f 0⟩)⟩
    apply Sigma.ext
    · rfl
    apply heq_of_eq
    funext i
    fin_cases i
    rfl
  s_comp_δ₀ n := by
    apply ConcreteCategory.hom_ext
    rintro ⟨a, f⟩
    apply Sigma.ext
    · rfl
    apply heq_of_eq
    funext i
    change Fin (n + 1) → S a at f
    change Fin (n + 1) at i
    change (Fin.cons (Classical.choice (show Nonempty (S a) from ⟨f 0⟩)) f :
      Fin (n + 2) → S a) (Fin.succAbove 0 i) = f i
    simp
  s_comp_δ n i := by
    apply ConcreteCategory.hom_ext
    rintro ⟨a, f⟩
    change Fin (n + 2) → S a at f
    change (⟨a, fun j : Fin (n + 2) =>
      (Fin.cons (Classical.choice (show Nonempty (S a) from ⟨f 0⟩)) f : Fin (n + 3) → S a)
        (i.succ.succAbove j)⟩ : Σ a : α, Fin (n + 2) → S a) =
      ⟨a, (Fin.cons (Classical.choice (show Nonempty (S a) from ⟨f 0⟩))
        (fun l => f (i.succAbove l)) : Fin (n + 2) → S a)⟩
    apply Sigma.ext
    · rfl
    apply heq_of_eq
    funext j
    change Fin (n + 2) → S a at f
    change Fin (n + 2) at j
    change (Fin.cons (Classical.choice (show Nonempty (S a) from ⟨f 0⟩)) f :
      Fin (n + 3) → S a) (i.succ.succAbove j) =
        (Fin.cons (Classical.choice (show Nonempty (S a) from ⟨f 0⟩))
          (fun l => f (i.succAbove l)) : Fin (n + 2) → S a) j
    exact Fin.cases (by simp) (fun j => by simp) j
  s_comp_σ n i := by
    apply ConcreteCategory.hom_ext
    rintro ⟨a, f⟩
    change Fin (n + 1) → S a at f
    change (⟨a, fun j : Fin (n + 3) =>
      (Fin.cons (Classical.choice (show Nonempty (S a) from ⟨f 0⟩)) f : Fin (n + 2) → S a)
        (i.succ.predAbove j)⟩ : Σ a : α, Fin (n + 3) → S a) =
      ⟨a, (Fin.cons (Classical.choice (show Nonempty (S a) from ⟨f 0⟩))
        (fun l => f (i.predAbove l)) : Fin (n + 3) → S a)⟩
    apply Sigma.ext
    · rfl
    apply heq_of_eq
    funext j
    change Fin (n + 1) → S a at f
    change Fin (n + 3) at j
    change (Fin.cons (Classical.choice (show Nonempty (S a) from ⟨f 0⟩)) f :
      Fin (n + 2) → S a) (i.succ.predAbove j) =
        (Fin.cons (Classical.choice (show Nonempty (S a) from ⟨f 0⟩))
          (fun l => f (i.predAbove l)) : Fin (n + 3) → S a) j
    exact Fin.cases (by simp) (fun j => by simp) j

variable (A : Type v) [Category.{w} A] [Abelian A] [HasCoproducts.{u} A] (M : A)

def coefficients : SimplicialObject.Augmented A :=
  ((SimplicialObject.Augmented.whiskering _ _).obj (sigmaConst.obj M)).obj (augmented S)

def complex : ChainComplex A ℕ :=
  (alternatingFaceMapComplex A).obj (coefficients S A M).left

def homotopyEquiv : HomotopyEquiv (complex S A M)
    ((ChainComplex.single₀ A).obj (coefficients S A M).right) :=
  ((extraDegeneracy S).map (sigmaConst.obj M)).homotopyEquiv

theorem exactAt (n : ℕ) (hn : n ≠ 0) : (complex S A M).ExactAt n := by
  have hz := HomologicalComplex.isZero_single_obj_X (ComplexShape.down ℕ) 0
    (coefficients S A M).right n hn
  have ht := HomologicalComplex.ExactAt.of_isZero hz
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  exact ht.isZero_homology.of_iso ((FiberTupleCech.homotopyEquiv S A M).toHomologyIso n)

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.FiberTuple.FiberTupleCech
