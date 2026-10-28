import OAI.AlgebraicGeometry.Comparison.Betti.HomQuasiIso
import Mathlib.Algebra.Homology.Factorizations.CM5a
import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives
import Mathlib.Algebra.Homology.DerivedCategory.KInjective

/-! # Injective Replacement -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Acyclic.InjectiveReplacement.Ext

noncomputable section

/-! Actual bounded-below injective replacements and their Hom cohomology comparison. -/

open _root_.CategoryTheory _root_.CategoryTheory.Abelian Opposite _root_.HomologicalComplex

universe u v w

variable {C : Type u} [Category.{v} C] [Abelian C] [EnoughInjectives C]
  (K : CochainComplex C ℤ) (n : ℤ) [K.IsStrictlyGE n]

def boundedInjectiveReplacement : CochainComplex C ℤ :=
  (CochainComplex.Plus.modelCategoryQuillen.exists_quasiIso_injective K n).choose

def boundedInjectiveReplacementMap : K ⟶ boundedInjectiveReplacement K n :=
  (CochainComplex.Plus.modelCategoryQuillen.exists_quasiIso_injective K n).choose_spec.choose

instance boundedInjectiveReplacementMap_quasiIso :
    QuasiIso (boundedInjectiveReplacementMap K n) :=
  (CochainComplex.Plus.modelCategoryQuillen.exists_quasiIso_injective K n).choose_spec.choose_spec.choose

instance boundedInjectiveReplacement_injective (p : ℤ) :
    Injective ((boundedInjectiveReplacement K n).X p) :=
  (CochainComplex.Plus.modelCategoryQuillen.exists_quasiIso_injective K n).choose_spec.choose_spec.choose_spec.choose p

instance boundedInjectiveReplacement_bound : (boundedInjectiveReplacement K n).IsStrictlyGE n :=
  (CochainComplex.Plus.modelCategoryQuillen.exists_quasiIso_injective K n).choose_spec.choose_spec.choose_spec.choose_spec

instance boundedInjectiveReplacement_isKInjective :
    (boundedInjectiveReplacement K n).IsKInjective :=
  CochainComplex.isKInjective_of_injective _ n

variable [HasExt.{w} C] (A : C)

theorem boundedInjectiveReplacementMap_hom_quasiIso
    (hExt : ∀ p q, Subsingleton (Ext A (K.X p) (q + 1))) :
    QuasiIso (((preadditiveCoyoneda.obj (op A)).mapHomologicalComplex (.up ℤ)).map
      (boundedInjectiveReplacementMap K n)) :=
  HomQuasiIso.Ext.integerHomComplex_map_quasiIso A (boundedInjectiveReplacementMap K n) n hExt
    (fun p q => Ext.subsingleton_of_injective A ((boundedInjectiveReplacement K n).X p) q)

def boundedInjectiveReplacementHomologyIso
    (hExt : ∀ p q, Subsingleton (Ext A (K.X p) (q + 1))) (p : ℤ) :
    (IntegerAcyclicHomComplex.Ext.integerHomComplex A K).homology p ≅
      (IntegerAcyclicHomComplex.Ext.integerHomComplex A (boundedInjectiveReplacement K n)).homology p := by
  let f : IntegerAcyclicHomComplex.Ext.integerHomComplex A K ⟶ IntegerAcyclicHomComplex.Ext.integerHomComplex A (boundedInjectiveReplacement K n) :=
    ((preadditiveCoyoneda.obj (op A)).mapHomologicalComplex (.up ℤ)).map
      (boundedInjectiveReplacementMap K n)
  have : QuasiIso f := boundedInjectiveReplacementMap_hom_quasiIso K n A hExt
  have : IsIso (homologyMap f p) :=
    (quasiIsoAt_iff_isIso_homologyMap f p).mp inferInstance
  exact asIso (homologyMap f p)

end

end OAI.AlgebraicGeometry.Comparison.Betti.Acyclic.InjectiveReplacement.Ext
