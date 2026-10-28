import OAI.NumberTheory.PadicHodge.IntegralComparison.Cochain.HomAcyclicProducts
import Mathlib.Algebra.Homology.HomologicalComplexAbelian

/-! # Lift Uniqueness -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Supported.LiftUniqueness

noncomputable section

/-! Supported lifts are unique up to actual cochain homotopy when
the coefficient Hom rows in the kernel are exact. A degreewise section
also allows a homotopy after forgetting support to be lifted. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.Preadditive _root_.HomologicalComplex
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
universe u v
variable {C : Type u} [Category.{v} C] [Abelian C]
  {K L M : CochainComplex C ℕ} (p : L ⟶ M)
  (hker : ∀ n, Cochain.HomAcyclic.Rows K ((kernel p).X n))

def null_of_comp_zero (f : K ⟶ L) (hf : f ≫ p = 0) : Homotopy f 0 :=
  (Homotopy.ofEq (kernel.lift_ι p f hf).symm).trans
    (((Cochain.HomAcyclic.null (kernel p) hker (kernel.lift p f hf)).compRight
      (kernel.ι p)).trans (Homotopy.ofEq (zero_comp)))

def of_comp_eq (f g : K ⟶ L) (hfg : f ≫ p = g ≫ p) : Homotopy f g :=
  Homotopy.equivSubZero.symm (null_of_comp_zero p hker (f - g)
    (by rw [sub_comp, hfg, sub_self]))

variable (σ : ∀ n, M.X n ⟶ L.X n) (hσ : ∀ n, σ n ≫ p.f n = 𝟙 _)
  (f g : K ⟶ L) (h : Homotopy (f ≫ p) (g ≫ p))

def correction : K ⟶ L := Homotopy.nullHomotopicMap (fun i j => h.hom i j ≫ σ j)

def correction_null : Homotopy (correction p σ f g h) 0 :=
  Homotopy.nullHomotopy _ (fun i j hij => by rw [h.zero i j hij, zero_comp])

include hσ in
theorem correction_comp : correction p σ f g h ≫ p = (f - g) ≫ p := by
  rw [correction, Homotopy.nullHomotopicMap_comp]
  have he : (fun i j => h.hom i j ≫ σ j ≫ p.f j) = h.hom := by
    funext i j
    rw [hσ, Category.comp_id]
  simp only [Category.assoc]
  rw [he]
  apply HomologicalComplex.Hom.ext
  funext n
  change dNext n h.hom + prevD n h.hom = (f.f n - g.f n) ≫ p.f n
  rw [sub_comp]
  exact (eq_sub_iff_add_eq).mpr (h.comm n).symm

def of_comp_homotopy : Homotopy f g := by
  let z := f - g - correction p σ f g h
  have hz : z ≫ p = 0 := by
    rw [show z = f - g - correction p σ f g h from rfl, sub_comp,
      correction_comp p σ hσ f g h, sub_self]
  refine Homotopy.equivSubZero.symm ?_
  refine (Homotopy.ofEq (show f - g = z + correction p σ f g h by dsimp [z]; abel)).trans ?_
  exact ((null_of_comp_zero p hker z hz).add (correction_null p σ f g h)).trans
    (Homotopy.ofEq (zero_add _))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Supported.LiftUniqueness
