import Mathlib.CategoryTheory.Sites.Abelian
import Mathlib.Algebra.Homology.Additive

/-! # Sheafification Complex -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.SheafificationComplex.SheafificationComplexUnit

noncomputable section

/-! The actual sheafification unit is a natural map of complexes. -/

open _root_.CategoryTheory

universe u v w z

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  {D : Type w} [Category.{z} D] [Abelian D] [HasSheafify J D]

def functor : CochainComplex (Cᵒᵖ ⥤ D) ℕ ⥤ CochainComplex (Cᵒᵖ ⥤ D) ℕ :=
  (presheafToSheaf J D).mapHomologicalComplex (.up ℕ) ⋙
    (sheafToPresheaf J D).mapHomologicalComplex (.up ℕ)

def unit (K : CochainComplex (Cᵒᵖ ⥤ D) ℕ) : K ⟶ (functor J).obj K where
  f n := toSheafify J (K.X n)
  comm' i j _ := (toSheafify_naturality J (K.d i j)).symm

theorem naturality {K L : CochainComplex (Cᵒᵖ ⥤ D) ℕ} (f : K ⟶ L) :
    unit J K ≫ (functor J).map f = f ≫ unit J L := by
  ext n : 1
  exact (toSheafify_naturality J (f.f n)).symm

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.SheafificationComplex.SheafificationComplexUnit
