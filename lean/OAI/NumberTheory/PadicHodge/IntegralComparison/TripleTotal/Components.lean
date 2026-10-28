import OAI.AlgebraicGeometry.Comparison.Betti.Finite.TotalFunctor
import Mathlib.Algebra.Homology.HomologicalComplexLimits
import Mathlib.Algebra.Homology.HomologicalComplexAbelian

/-! # Components -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TripleTotal.Components

noncomputable section

/-! The two bracketings of a genuine first-quadrant triple complex,
with their canonical degreewise coproduct injections. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.Preadditive

universe u v
variable {A : Type u} [Category.{v} A] [Abelian A] [HasFiniteCoproducts A]

local instance total (K : HomologicalComplex₂ A (.up ℕ) (.up ℕ)) :
    K.HasTotal (.up ℕ) := AlgebraicGeometry.Comparison.Betti.TotalExists.hasTotal_of_finiteCoproducts K
local instance complexTotal (K : HomologicalComplex₂ (CochainComplex A ℕ) (.up ℕ) (.up ℕ)) :
    K.HasTotal (.up ℕ) := AlgebraicGeometry.Comparison.Betti.TotalExists.hasTotal_of_finiteCoproducts K

local instance totalAdditive :
    (HomologicalComplex₂.totalFunctor A (.up ℕ) (.up ℕ) (.up ℕ)).Additive where
  map_add {K L} f g := by
    apply HomologicalComplex.Hom.ext
    funext n
    apply HomologicalComplex₂.total.hom_ext
    intro i j hij
    change K.ιTotal (.up ℕ) i j n hij ≫
      (HomologicalComplex₂.total.map (f + g) (.up ℕ)).f n = _
    change K.ιTotal (.up ℕ) i j n hij ≫
      (HomologicalComplex₂.total.map (f + g) (.up ℕ)).f n =
        K.ιTotal (.up ℕ) i j n hij ≫
          ((HomologicalComplex₂.total.map f (.up ℕ)).f n +
            (HomologicalComplex₂.total.map g (.up ℕ)).f n)
    rw [comp_add, HomologicalComplex₂.ιTotal_map, HomologicalComplex₂.ιTotal_map,
      HomologicalComplex₂.ιTotal_map]
    rw [HomologicalComplex.add_f_apply, HomologicalComplex.add_f_apply, add_comp]

variable (T : HomologicalComplex₂ (CochainComplex A ℕ) (.up ℕ) (.up ℕ))

def leftBicomplex : HomologicalComplex₂ A (.up ℕ) (.up ℕ) := T.total (.up ℕ)

def rightBicomplex : HomologicalComplex₂ A (.up ℕ) (.up ℕ) :=
  ((HomologicalComplex₂.totalFunctor A (.up ℕ) (.up ℕ) (.up ℕ)).mapHomologicalComplex (.up ℕ)).obj T

def left : CochainComplex A ℕ := (leftBicomplex T).total (.up ℕ)
def right : CochainComplex A ℕ := (rightBicomplex T).total (.up ℕ)

def leftInjection (r i j N : ℕ) (h : r + i + j = N) :
    ((T.X r).X i).X j ⟶ (left T).X N :=
  (T.ιTotal (.up ℕ) r i (r + i) rfl).f j ≫
    (leftBicomplex T).ιTotal (.up ℕ) (r + i) j N h

def rightInjection (r i j N : ℕ) (h : r + i + j = N) :
    ((T.X r).X i).X j ⟶ (right T).X N :=
  HomologicalComplex₂.ιTotal (T.X r) (.up ℕ) i j (i + j) rfl ≫
    (rightBicomplex T).ιTotal (.up ℕ) r (i + j) N (by change r + (i + j) = N; omega)

theorem leftInjection_eq (r i s j N : ℕ) (hri : r + i = s) (hN : s + j = N) :
    leftInjection T r i j N (by omega) =
      (T.ιTotal (.up ℕ) r i s hri).f j ≫
        (leftBicomplex T).ιTotal (.up ℕ) s j N hN := by
  subst s
  rfl

theorem rightInjection_eq (r i j s N : ℕ) (hij : i + j = s) (hN : r + s = N) :
    rightInjection T r i j N (by omega) =
      HomologicalComplex₂.ιTotal (T.X r) (.up ℕ) i j s hij ≫
        (rightBicomplex T).ιTotal (.up ℕ) r s N hN := by
  subst s
  rfl

def component (N : ℕ) : (right T).X N ⟶ (left T).X N :=
  (rightBicomplex T).totalDesc (c₁₂ := .up ℕ) (fun r s hrs =>
    HomologicalComplex₂.totalDesc (T.X r) (c₁₂ := .up ℕ) (fun i j hij =>
      leftInjection T r i j N (by change r + s = N at hrs; change i + j = s at hij; omega)))

@[reassoc]
theorem rightInjection_component (r i j N : ℕ) (h : r + i + j = N) :
    rightInjection T r i j N h ≫ component T N = leftInjection T r i j N h := by
  dsimp only [rightInjection, component]
  erw [Category.assoc, HomologicalComplex₂.ι_totalDesc, HomologicalComplex₂.ι_totalDesc]

theorem right_hom_ext {V : A} (N : ℕ) {f g : (right T).X N ⟶ V}
    (hfg : ∀ r i j (h : r + i + j = N), rightInjection T r i j N h ≫ f =
      rightInjection T r i j N h ≫ g) : f = g := by
  apply HomologicalComplex₂.total.hom_ext
  intro r s hrs
  change r + s = N at hrs
  apply HomologicalComplex₂.total.hom_ext
  intro i j hij
  change i + j = s at hij
  subst s
  have ht := hfg r i j (by omega)
  dsimp only [rightInjection] at ht
  erw [Category.assoc, Category.assoc] at ht
  exact ht

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TripleTotal.Components
