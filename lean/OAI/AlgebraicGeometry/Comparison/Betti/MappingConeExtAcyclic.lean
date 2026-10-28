import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import Mathlib.CategoryTheory.ConcreteCategory.EpiMono

/-! # Mapping Cone Ext Acyclic -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.MappingConeExtAcyclic

noncomputable section

/-! Bounds and termwise Ext vanishing for the actual mapping cone. -/

open _root_.CategoryTheory _root_.CategoryTheory.Abelian _root_.CategoryTheory.Limits Opposite

universe u v w

variable {C : Type u} [Category.{v} C] [Abelian C]
  {K L : CochainComplex C ℤ} (f : K ⟶ L)

theorem mappingCone_isStrictlyGE (n : ℤ) [K.IsStrictlyGE n] [L.IsStrictlyGE n] :
    (CochainComplex.mappingCone f).IsStrictlyGE (n - 1) := by
  rw [CochainComplex.isStrictlyGE_iff]
  intro i hi
  exact (CochainComplex.mappingCone.isZero_X_iff f i).mpr
    ⟨K.isZero_of_isStrictlyGE n (i + 1) (by omega),
      L.isZero_of_isStrictlyGE n i (by omega)⟩

variable [HasExt.{w} C] (A : C)

theorem mappingCone_termExt_acyclic
    (hK : ∀ p q, Subsingleton (Ext A (K.X p) (q + 1)))
    (hL : ∀ p q, Subsingleton (Ext A (L.X p) (q + 1))) (p : ℤ) (q : ℕ) :
    Subsingleton (Ext A ((CochainComplex.mappingCone f).X p) (q + 1)) := by
  let H := (extFunctor.{w} (q + 1) : Cᵒᵖ ⥤ C ⥤ AddCommGrpCat.{w}).obj (op A)
  have := hK (p + 1) q
  have := hL p q
  have : Subsingleton (H.obj (K.X (p + 1) ⊞ L.X p)) :=
    Ext.addEquivBiprod.injective.subsingleton
  let e := H.mapIso (HomologicalComplex.homotopyCofiber.XIsoBiprod f p (p + 1) rfl)
  exact (ConcreteCategory.bijective_of_isIso e.hom).injective.subsingleton

end

end OAI.AlgebraicGeometry.Comparison.Betti.MappingConeExtAcyclic
