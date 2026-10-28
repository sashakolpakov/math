import OAI.AlgebraicGeometry.Comparison.Betti.AbCochainClasses
import OAI.AlgebraicGeometry.Comparison.Betti.HomComplexSingleIso

/-! # Hom Cocycle Classes -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.HomCocycleClasses.Ext

noncomputable section

/-! The Hom-complex identification sends actual cocycles to their original quotient classes. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CochainComplex _root_.CochainComplex.HomComplex

universe u v

variable {C : Type u} [Category.{v} C] [Abelian C]

theorem homComplexCohomology_class (F G : CochainComplex C ℤ) (n : ℤ)
    (z : Cocycle F G n) :
    homologyAddEquiv F G n
      (AbCochainClasses.Homology.cochainClass (HomComplex F G) n z.1 z.2) = CohomologyClass.mk z := by
  let J := HomComplex F G
  let D := leftHomologyData F G n
  let c := AbCochainClasses.Homology.cycle J n z.1 z.2
  have hc : D.cyclesIso.hom c = z := by
    apply Subtype.ext
    have h := congrArg (fun g : J.cycles n ⟶ J.X n => g.hom c) D.cyclesIso_hom_comp_i
    exact h.trans (AbCochainClasses.Homology.cycle_i J n z.1 z.2)
  have h := congrArg (fun g : J.cycles n ⟶ D.H => g.hom c) D.homologyπ_comp_homologyIso_hom
  change D.homologyIso.hom (J.homologyπ n c) = CohomologyClass.mk z
  exact h.trans (congrArg D.π hc)

theorem integerHomCohomologyClassEquiv_class (A : C) (K : CochainComplex C ℤ) (n : ℤ)
    (f : A ⟶ K.X n) (hf : f ≫ K.d n (n + 1) = 0) :
    HomComplexSingleIso.Ext.integerHomCohomologyClassEquiv A K n
      (AbCochainClasses.Homology.cochainClass (IntegerAcyclicHomComplex.Ext.integerHomComplex A K) n f hf) =
        CohomologyClass.mk (Cocycle.fromSingleMk f (zero_add n) (n + 1) rfl hf) := by
  let e := HomComplexSingleIso.Ext.integerHomSingleIso A K
  change homologyAddEquiv _ K n
    (HomologicalComplex.homologyMap e.hom n
      (AbCochainClasses.Homology.cochainClass (IntegerAcyclicHomComplex.Ext.integerHomComplex A K) n f hf)) = _
  have h := AbCochainClasses.Homology.cochainClass_naturality n e.hom f hf
  exact (congrArg (homologyAddEquiv _ K n) h).trans
    (homComplexCohomology_class _ K n
      (Cocycle.fromSingleMk f (zero_add n) (n + 1) rfl hf))

end

end OAI.AlgebraicGeometry.Comparison.Betti.HomCocycleClasses.Ext
