import OAI.AlgebraicGeometry.HodgeConjecture.CMReduction.IteratedCup

/-! # Cup Append -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMReduction.CupAppend.CM.Construction

noncomputable section

section

/-! Naturality and small-degree normalizations of the actual iterated cup. -/

open _root_.CategoryTheory

theorem cupUnit_pullback {R : Type} [CommRing R]
    {X Y : TopCat.{0}} (f : X ⟶ Y) :
    AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of R R) f 0
      (AlgebraicTopology.Products.CupCohomologyAlgebra.singularCohomologyCupUnit Y) = AlgebraicTopology.Products.CupCohomologyAlgebra.singularCohomologyCupUnit X := by
  change AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of R R) f 0
    (AlgebraicTopology.Cohomology.Singular.Representatives.singularClass (ModuleCat.of R R) Y 0 (AlgebraicTopology.Products.CupCohomologyAlgebra.cocycleCupUnit (TopCat.toSSet.obj Y))) =
      AlgebraicTopology.Cohomology.Singular.Representatives.singularClass (ModuleCat.of R R) X 0 (AlgebraicTopology.Products.CupCohomologyAlgebra.cocycleCupUnit (TopCat.toSSet.obj X))
  rw [AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality.singularCohomologyPullback_class]
  apply congrArg (AlgebraicTopology.Cohomology.Singular.Representatives.singularClass (ModuleCat.of R R) X 0)
  apply Subtype.ext
  exact AlgebraicTopology.Products.Cup.cupUnit_pullback (TopCat.toSSet.map f)

theorem h1Cup_pullback {R : Type} [CommRing R]
    {X Y : TopCat.{0}} (f : X ⟶ Y) (n : ℕ)
    (v : Fin n → AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of R R) Y 1) :
    AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of R R) f n (IteratedCup.CM.Construction.h1Cup R Y n v) =
      IteratedCup.CM.Construction.h1Cup R X n (fun i => AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of R R) f 1 (v i)) := by
  induction n with
  | zero => exact cupUnit_pullback f
  | succ n ih =>
    rw [IteratedCup.CM.Construction.h1Cup_succ, IteratedCup.CM.Construction.h1Cup_succ, CupPullback.CM.Construction.cup_pullback, ih]
    rfl

theorem scheme_h1Cup_pullback {R : Type} [CommRing R]
    {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase} (f : X ⟶ Y) (n : ℕ)
    (v : Fin n → Betti.Scheme.schemeBetti (ModuleCat.of R R) Y 1) :
    Betti.Scheme.schemeBettiMap (ModuleCat.of R R) n f (IteratedCup.CM.Construction.h1Cup R (Betti.Scheme.schemePointSpace Y) n v) =
      IteratedCup.CM.Construction.h1Cup R (Betti.Scheme.schemePointSpace X) n
        (fun i => Betti.Scheme.schemeBettiMap (ModuleCat.of R R) 1 f (v i)) :=
  h1Cup_pullback (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map f) n v

theorem h1Cup_one {R : Type} [CommRing R] (X : TopCat.{0})
    (v : Fin 1 → AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of R R) X 1) :
    IteratedCup.CM.Construction.h1Cup R X 1 v = v 0 :=
  AlgebraicTopology.Products.CupCohomologyAlgebra.cohomologyCupUnit_cup (TopCat.toSSet.obj X) (v 0)

theorem h1Cup_two {R : Type} [CommRing R] (X : TopCat.{0})
    (v : Fin 2 → AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of R R) X 1) :
    IteratedCup.CM.Construction.h1Cup R X 2 v = AlgebraicTopology.Products.CupCohomology.singularCohomologyCup X 1 1 (v 0) (v 1) := by
  rw [IteratedCup.CM.Construction.h1Cup_succ, h1Cup_one]
  rfl

theorem h1Cup_four {R : Type} [CommRing R] (X : TopCat.{0})
    (v : Fin 4 → AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of R R) X 1) :
    IteratedCup.CM.Construction.h1Cup R X 4 v = AlgebraicTopology.Products.CupCohomology.singularCohomologyCup X 2 2
      (AlgebraicTopology.Products.CupCohomology.singularCohomologyCup X 1 1 (v 0) (v 1))
      (AlgebraicTopology.Products.CupCohomology.singularCohomologyCup X 1 1 (v 2) (v 3)) := by
  rw [IteratedCup.CM.Construction.h1Cup_succ R X 3 v, IteratedCup.CM.Construction.h1Cup_succ R X 2 (Fin.init v),
    h1Cup_two X (Fin.init (Fin.init v))]
  exact AlgebraicTopology.Products.CupCohomologyAlgebra.cohomologyCup_assoc (R := R) (p := 2) (q := 1) (r := 1) (TopCat.toSSet.obj X)
    (AlgebraicTopology.Products.CupCohomology.singularCohomologyCup X 1 1 (v 0) (v 1)) (v 2) (v 3)

end

/-! Grouping consecutive blocks in an actual iterated H1 cup product. -/

open _root_.CategoryTheory

theorem h1Cup_snoc {R : Type} [CommRing R] (X : TopCat.{0}) (n : ℕ)
    (v : Fin n → AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of R R) X 1)
    (x : AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of R R) X 1) :
    IteratedCup.CM.Construction.h1Cup R X (n + 1) (Fin.snoc v x) =
      AlgebraicTopology.Products.CupCohomology.singularCohomologyCup X n 1 (IteratedCup.CM.Construction.h1Cup R X n v) x := by
  rw [IteratedCup.CM.Construction.h1Cup_succ R X n (Fin.snoc v x), Fin.init_snoc, Fin.snoc_last]

theorem h1Cup_append {R : Type} [CommRing R] (X : TopCat.{0}) (n m : ℕ)
    (u : Fin n → AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of R R) X 1)
    (v : Fin m → AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of R R) X 1) :
    IteratedCup.CM.Construction.h1Cup R X (n + m) (Fin.append u v) =
      AlgebraicTopology.Products.CupCohomology.singularCohomologyCup X n m (IteratedCup.CM.Construction.h1Cup R X n u) (IteratedCup.CM.Construction.h1Cup R X m v) := by
  induction m with
  | zero =>
    have hv : Fin.append u v = u := by
      simpa only [Fin.cast_refl, Function.comp_id] using Fin.append_right_nil u v rfl
    rw [hv]
    exact (AlgebraicTopology.Products.CupCohomologyAlgebra.cohomologyCup_cupUnit (R := R) (p := n) (TopCat.toSSet.obj X) (IteratedCup.CM.Construction.h1Cup R X n u)).symm
  | succ m ih =>
    conv_lhs => rw [← Fin.snoc_init_self v, Fin.append_snoc]
    erw [h1Cup_snoc (R := R) X (n + m) (Fin.append u (Fin.init v)) (v (Fin.last m)),
      ih, IteratedCup.CM.Construction.h1Cup_succ R X m v]
    exact AlgebraicTopology.Products.CupCohomologyAlgebra.cohomologyCup_assoc (R := R) (p := n) (q := m) (r := 1)
      (TopCat.toSSet.obj X) (IteratedCup.CM.Construction.h1Cup R X n u) (IteratedCup.CM.Construction.h1Cup R X m (Fin.init v)) (v (Fin.last m))

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMReduction.CupAppend.CM.Construction
