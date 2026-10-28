import OAI.NumberTheory.PadicHodge.IntegralComparison.NonemptyCechNerve
import OAI.AlgebraicGeometry.Crystalline.Cohomology.HomotopyOppositeUnop
import Mathlib.AlgebraicTopology.ExtraDegeneracy
import Mathlib.CategoryTheory.Limits.Preorder

/-! # Cech Contraction -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Semilattice.CechContraction.SemilatticeCechContraction

noncomputable section

/-! A Čech contraction in a meet semilattice with a greatest element.
This applies to affine opens contained in one fixed affine chart. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite Simplicial

universe u w t z
variable (C : Type u) [SemilatticeInf C] [OrderTop C]
  {ι : Type w} (U : ι → C)

omit [OrderTop C] in
/-- Over a preorder, a map of formal coproducts is determined by
its function on components. -/
theorem hom_ext_indices {S T : FormalCoproduct.{w} C} {f g : S ⟶ T}
    (h : f.f = g.f) : f = g :=
  FormalCoproduct.hom_ext h (fun _ => Subsingleton.elim _ _)

/-- The Čech nerve augmented to the greatest element. -/
def augmented : SimplicialObject.Augmented (FormalCoproduct.{w} C) where
  left := IntegralComparison.NonemptyCechNerve.nerve U
  right := (FormalCoproduct.incl C).obj ⊤
  hom :=
    { app _ := { f := fun _ => PUnit.unit, φ := fun _ => homOfLE le_top }
      naturality _ _ _ := hom_ext_indices C rfl }

variable (i₀ : ι) (hU : U i₀ = ⊤)

/-- Select the greatest member in degree zero. -/
def sectionZero : (augmented C U).right ⟶ (augmented C U).left _⦋0⦌ where
  f _ _ := i₀
  φ _ := Pi.lift (fun _ => homOfLE (by change ⊤ ≤ U i₀; rw [hU]))

/-- Insert the greatest member at the start of a tuple. -/
def insert (n : ℕ) : (augmented C U).left _⦋n⦌ ⟶ (augmented C U).left _⦋n + 1⦌ where
  f v := Fin.cons i₀ v
  φ v := Pi.lift (Fin.cases (homOfLE (by
      change (∏ᶜ (U ∘ v)) ≤ U i₀
      rw [hU]
      exact le_top))
    (fun j => Pi.π (U ∘ v) j))

/-- The insertion satisfies the simplicial contraction identities. -/
def extraDegeneracy : SimplicialObject.Augmented.ExtraDegeneracy (augmented C U) where
  s' := sectionZero C U i₀ hU
  s := insert C U i₀ hU
  s'_comp_ε := by
    apply hom_ext_indices C
    funext v
    cases v
    rfl
  s₀_comp_δ₁ := by
    apply hom_ext_indices C
    funext v j
    fin_cases j
    rfl
  s_comp_δ₀ n := by
    apply hom_ext_indices C
    funext v j
    change Fin (n + 1) → ι at v
    change Fin (n + 1) at j
    change (Fin.cons i₀ v : Fin (n + 2) → ι) (Fin.succAbove 0 j) = v j
    simp
  s_comp_δ n i := by
    apply hom_ext_indices C
    funext v j
    change Fin (n + 2) → ι at v
    change Fin (n + 2) at j
    change (Fin.cons i₀ v : Fin (n + 3) → ι) (i.succ.succAbove j) =
      (Fin.cons i₀ (fun a => v (i.succAbove a)) : Fin (n + 2) → ι) j
    refine Fin.cases ?_ (fun j => ?_) j
    · simp
    · simp
  s_comp_σ n i := by
    apply hom_ext_indices C
    funext v j
    change Fin (n + 1) → ι at v
    change Fin (n + 3) at j
    change (Fin.cons i₀ v : Fin (n + 2) → ι) (i.succ.predAbove j) =
      (Fin.cons i₀ (fun a => v (i.predAbove a)) : Fin (n + 3) → ι) j
    refine Fin.cases ?_ (fun j => ?_) j
    · simp
    · simp

variable {A : Type t} [Category.{z} A] [Preadditive A] [HasProducts.{w} A] [HasZeroObject A]
  (P : Cᵒᵖ ⥤ A)

def point : A :=
  ((FormalCoproduct.evalOp.{w} C A).obj P).obj (op ((FormalCoproduct.incl.{w} C).obj ⊤))

def pointIso : point C P ≅ P.obj (op ⊤) :=
  ((FormalCoproduct.evalOpCompInlIsoId.{w} C A).app P).app (op ⊤)

def coefficientsExtraDegeneracy :=
  (extraDegeneracy C U i₀ hU).map (((FormalCoproduct.evalOp C A).obj P).rightOp)

def homotopyEquiv : HomotopyEquiv ((CochainComplex.single₀ A).obj (P.obj (op ⊤)))
    ((IntegralComparison.NonemptyCechNerve.complexFunctor U).obj P) :=
  (((HomotopyEquiv.ofIso (AlgebraicGeometry.Crystalline.Cohomology.HomotopyOppositeUnop.HomotopyOpposite.cofaceIso
    ((FormalCoproduct.cosimplicialObjectFunctor (IntegralComparison.NonemptyCechNerve.nerve U)).obj P)).symm).trans
      (AlgebraicGeometry.Crystalline.Cohomology.HomotopyOppositeUnop.HomotopyOpposite.unop (coefficientsExtraDegeneracy C U i₀ hU P).homotopyEquiv)).trans
        (HomotopyEquiv.ofIso (AlgebraicGeometry.Crystalline.Cohomology.HomotopyOppositeUnop.HomotopyOpposite.singleIso (point C P)))).trans
          (HomotopyEquiv.ofIso ((CochainComplex.single₀ A).mapIso (pointIso C P))) |>.symm

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Semilattice.CechContraction.SemilatticeCechContraction
