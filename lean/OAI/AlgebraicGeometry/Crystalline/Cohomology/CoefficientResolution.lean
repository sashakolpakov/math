import OAI.AlgebraicGeometry.Crystalline.Cohomology.ConstantSheaf
import Mathlib.CategoryTheory.Abelian.Injective.Ext
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-! # Coefficient Resolution -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.CoefficientResolution.CoefficientResolutionExactness

noncomputable section

/-! # Vanishing original coefficient Ext makes the section complex of an injective resolution exact -/

open _root_.CategoryTheory _root_.CategoryTheory.Abelian Opposite

universe u

variable (R : Type u) [CommRing R] (X : TopCat.{u})

local notation "V" => OAI.AlgebraicGeometry.Crystalline.Cohomology.ConstantSheaf.ConstantSheafSections.Sheaves R X
local notation "A" => OAI.AlgebraicGeometry.Crystalline.Cohomology.ConstantSheaf.ConstantSheafSections.coefficient R X

local instance coefficientExt : HasExt.{u + 1} V := HasExt.standard _

abbrev sections : V ⥤ ModuleCat.{u} R :=
  (sheafSections (Opens.grothendieckTopology X) (ModuleCat.{u} R)).obj (op ⊤)

theorem section_exact {F : V} (I : InjectiveResolution F) (n : ℕ)
    [Subsingleton (Ext.{u + 1} A F (n + 1))]
    (x : (I.cocomplex.X (n + 1)).obj.obj (op ⊤))
    (hx : (I.cocomplex.d (n + 1) (n + 2)).hom.app (op ⊤) x = 0) :
    ∃ y : (I.cocomplex.X n).obj.obj (op ⊤),
      (I.cocomplex.d n (n + 1)).hom.app (op ⊤) y = x := by
  let e (j : ℕ) := ConstantSheaf.ConstantSheafSections.linearEquiv R X (I.cocomplex.X j)
  let f : A ⟶ I.cocomplex.X (n + 1) := (e (n + 1)).symm x
  have hf : f ≫ I.cocomplex.d (n + 1) (n + 2) = 0 := by
    apply (e (n + 2)).injective
    rw [map_zero]
    exact (ConstantSheaf.ConstantSheafSections.naturality R X f (I.cocomplex.d (n + 1) (n + 2))).trans
      ((congrArg ((I.cocomplex.d (n + 1) (n + 2)).hom.app (op ⊤))
        ((e (n + 1)).apply_symm_apply x)).trans hx)
  have hz : I.extMk f (n + 2) rfl hf = 0 := Subsingleton.elim _ _
  obtain ⟨g, hg⟩ := (I.extMk_eq_zero_iff f (n + 2) rfl hf n rfl).mp hz
  refine ⟨e n g, ?_⟩
  exact (ConstantSheaf.ConstantSheafSections.naturality R X g (I.cocomplex.d n (n + 1))).symm.trans
    ((congrArg (e (n + 1)) hg).trans ((e (n + 1)).apply_symm_apply x))

theorem exactAt {F : V} (I : InjectiveResolution F) (n : ℕ)
    [Subsingleton (Ext.{u + 1} A F (n + 1))] :
    (((sections R X).mapHomologicalComplex (.up ℕ)).obj I.cocomplex).ExactAt (n + 1) := by
  rw [HomologicalComplex.exactAt_iff' _ n (n + 1) (n + 2) (by simp) (by simp)]
  exact (ShortComplex.moduleCat_exact_iff _).mpr (section_exact R X I n)

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.CoefficientResolution.CoefficientResolutionExactness
