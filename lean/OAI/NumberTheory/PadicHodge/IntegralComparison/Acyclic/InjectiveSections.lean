import OAI.NumberTheory.PadicHodge.IntegralComparison.Acyclic.MapQuasiIso
import OAI.NumberTheory.PadicHodge.IntegralComparison.InjectiveSectionCohomology

/-! # Injective Sections -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Acyclic.InjectiveSections

noncomputable section

/-!
# IntegralComparison: an actual acyclic-resolution comparison computes the same original injective sections
-/

open _root_.CategoryTheory

open Abelian

universe u v z t

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{z} C]
  (R : Type t) [CommRing R] [Linear R C] (X : C)
  (K : CochainComplex C ℕ) {Z : C} (ι : (CochainComplex.single₀ C).obj Z ⟶ K)
  [QuasiIso ι] (I : InjectiveResolution Z) (a : K ⟶ I.cocomplex)

def map : Resolution.Comparison.complex R X K ⟶ InjectiveSectionCohomology.complex R X I :=
  ((IntegralComparison.Ext.ModuleFunctor.functor R X 0).mapHomologicalComplex (ComplexShape.up ℕ)).map a

variable (ha : ι ≫ a = I.ι) (hK : ∀ n q, Subsingleton (Ext.{z} X (K.X n) (q + 1)))

include ha hK in
theorem quasiIso : QuasiIso (InjectiveSections.map R X K I a) := by
  have h : ι ≫ a = (CochainComplex.single₀ C).map (𝟙 Z) ≫ I.ι :=
    ha.trans ((Category.id_comp I.ι).symm.trans (congrArg (fun b => b ≫ I.ι) ((CochainComplex.single₀ C).map_id Z).symm))
  exact MapQuasiIso.quasiIso R X ι I.ι a (𝟙 Z) h hK
    (fun n q => Ext.subsingleton_of_injective X (I.cocomplex.X n) q)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Acyclic.InjectiveSections
