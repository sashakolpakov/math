import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Definitions
import OAI.AlgebraicTopology.Products.CupCohomologyAlgebra
import OAI.AlgebraicTopology.Products.CupGradedCommutativity
import Mathlib.LinearAlgebra.Dual.Lemmas

/-! # Cohomology -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Cohomology.Construction

noncomputable section

/-!
# ProjectionFormula: cohomological projection formula

The statement module is imported only for its actual singular-cohomology
definitions and PoincareData. Its two unfinished target theorems are never
used. The final axiom audit checks this transitively.
-/

open _root_.CategoryTheory
open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Definitions

abbrev cup (X : TopCat.{0}) (p q : ℕ) :=
  AlgebraicTopology.Products.CupCohomology.singularCohomologyCup (R := ℚ) X p q

abbrev pull {X Y : TopCat.{0}} (f : X ⟶ Y) (p : ℕ) :=
  AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of ℚ ℚ) f p

abbrev ev (X : TopCat.{0}) (p : ℕ) :=
  AlgebraicTopology.Cohomology.Singular.Evaluation.singularEvaluation (ModuleCat.of ℚ ℚ) X p

/-- Integration against the specified fundamental class, with degree transport. -/
def integral {X : TopCat.{0}} {d : ℕ} (D : Definitions.PoincareData X d)
    (k : ℕ) (h : k = d) : Definitions.HQ X k →ₗ[ℚ] ℚ :=
  ((ev X d).flip D.fundamental).comp
    (AlgebraicTopology.Products.CupCohomologyAlgebra.cohomologyCast (TopCat.toSSet.obj X) (ModuleCat.of ℚ ℚ) h)

theorem integral_degreeCast {X : TopCat.{0}} {d : ℕ} (D : Definitions.PoincareData X d)
    {k l : ℕ} (h : k = l) (hk : k = d) (hl : l = d) (a : Definitions.HQ X k) :
    integral D l hl
        (AlgebraicTopology.Products.CupCohomologyAlgebra.cohomologyCast (TopCat.toSSet.obj X) (ModuleCat.of ℚ ℚ) h a) =
      integral D k hk a := by
  subst l
  rfl

theorem integral_eq_evaluation {X : TopCat.{0}} {d : ℕ} (D : Definitions.PoincareData X d)
    (k : ℕ) (h : k = d) (a : Definitions.HQ X k) :
    integral D k h a =
      ev X k a (cast (congrArg (fun j => (Definitions.BQ X j : Type)) h.symm) D.fundamental) := by
  subst d
  rfl

def pairing {X : TopCat.{0}} {d p q : ℕ} (D : Definitions.PoincareData X d)
    (h : p + q = d) (a : Definitions.HQ X p) (b : Definitions.HQ X q) : ℚ :=
  integral D (p + q) h (cup X p q a b)

theorem pairing_assoc {X : TopCat.{0}} {d p q r : ℕ}
    (D : Definitions.PoincareData X d)
    (hleft : (p + q) + r = d) (hright : p + (q + r) = d)
    (a : Definitions.HQ X p) (b : Definitions.HQ X q) (c : Definitions.HQ X r) :
    pairing D hleft (cup X p q a b) c =
      pairing D hright a (cup X q r b c) := by
  unfold pairing
  change integral D ((p + q) + r) hleft
      (AlgebraicTopology.Products.CupCohomology.cohomologyCup (TopCat.toSSet.obj X) (p + q) r
        (AlgebraicTopology.Products.CupCohomology.cohomologyCup (TopCat.toSSet.obj X) p q a b) c) = _
  rw [← AlgebraicTopology.Products.CupCohomologyAlgebra.cohomologyCup_assoc (TopCat.toSSet.obj X) a b c]
  exact (integral_degreeCast D (Nat.add_assoc p q r) hleft hright _).symm

theorem pairing_comm {X : TopCat.{0}} {d p q : ℕ}
    (D : Definitions.PoincareData X d) (h : p + q = d) (h' : q + p = d)
    (a : Definitions.HQ X p) (b : Definitions.HQ X q) :
    pairing D h a b = (-1 : ℚ) ^ (p * q) * pairing D h' b a := by
  unfold pairing cup
  rw [AlgebraicTopology.Products.CupGradedCommutativity.singularCohomologyCup_graded_comm, map_smul,
    integral_degreeCast D (Nat.add_comm q p) h' h]
  rfl

/-- The sign in the specification makes duality adjoint to `test ∪ class`. -/
theorem evaluation_duality {X : TopCat.{0}} {d p q : ℕ}
    (D : Definitions.PoincareData X d) (h : p + q = d) (h' : q + p = d)
    (a : Definitions.HQ X p) (b : Definitions.HQ X q) :
    ev X q b (D.duality p q h a) = pairing D h' b a := by
  rw [D.duality_apply, map_smul]
  rw [← AlgebraicTopology.Products.CapCompatibility.singularCohomologyCup_evaluation_cap]
  rw [← integral_eq_evaluation D (p + q) h]
  change (-1 : ℚ) ^ (p * q) * pairing D h a b = _
  rw [pairing_comm D h h' a b, ← mul_assoc, ← mul_pow]
  norm_num

/-- Actual singular cohomology separates rational homology classes. -/
theorem homology_ext (X : TopCat.{0}) (p : ℕ) {u v : Definitions.BQ X p}
    (h : ∀ a : Definitions.HQ X p, ev X p a u = ev X p a v) : u = v := by
  apply sub_eq_zero.mp
  apply (Module.forall_dual_apply_eq_zero_iff ℚ (u - v)).mp
  intro φ
  obtain ⟨a, rfl⟩ := (AlgebraicTopology.Cohomology.Singular.UniversalCoefficient.singularUniversalCoefficientEquiv (F := ℚ) X p).surjective φ
  rw [map_sub, AlgebraicTopology.Cohomology.Singular.UniversalCoefficient.singularUniversalCoefficientEquiv_apply]
  exact sub_eq_zero.mpr (h a)

theorem pairing_ext_right {X : TopCat.{0}} {d p q : ℕ}
    (D : Definitions.PoincareData X d) (h : p + q = d) {a b : Definitions.HQ X q}
    (hab : ∀ c : Definitions.HQ X p, pairing D h c a = pairing D h c b) : a = b := by
  have h' : q + p = d := (Nat.add_comm q p).trans h
  apply (D.duality q p h').injective
  apply homology_ext X p
  intro c
  simpa only [evaluation_duality D h' h] using hab c

/-- Integration adjunction for the pushforward defined by Poincare duality. -/
theorem pairing_pushforward {X Y : TopCat.{0}} {m n a b r : ℕ}
    (DX : Definitions.PoincareData X m) (DY : Definitions.PoincareData Y n) (f : X ⟶ Y)
    (hX : a + r = m) (hY : b + r = n)
    (hX' : r + a = m) (hY' : r + b = n)
    (c : Definitions.HQ Y r) (u : Definitions.HQ X a) :
    pairing DY hY' c (Definitions.pushforward DX DY f a b r hX hY u) =
      pairing DX hX' (pull f r c) u := by
  rw [← evaluation_duality DY hY hY', ← evaluation_duality DX hX hX']
  change ev Y r c
      (DY.duality b r hY ((DY.duality b r hY).symm
        (AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.singularHomologyPushforward (R := ℚ) f r (DX.duality a r hX u)))) = _
  rw [LinearEquiv.apply_symm_apply]
  exact (AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.singularEvaluation_naturality (ModuleCat.of ℚ ℚ) f r c
    (DX.duality a r hX u)).symm

/-- Pullback preserves the actual cup product, proved on cocycle representatives. -/
theorem pull_cup {X Y : TopCat.{0}} (f : X ⟶ Y) (p q : ℕ)
    (a : Definitions.HQ Y p) (b : Definitions.HQ Y q) :
    pull f (p + q) (cup Y p q a b) = cup X p q (pull f p a) (pull f q b) := by
  obtain ⟨a, rfl⟩ := AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass_surjective (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℚ ℚ) Y) p a
  obtain ⟨b, rfl⟩ := AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass_surjective (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℚ ℚ) Y) q b
  change HomologicalComplex.homologyMap
      (AlgebraicTopology.Cohomology.Singular.Functor.simplicialPullback (ModuleCat.of ℚ ℚ) (TopCat.toSSet.map f)) (p + q)
      (AlgebraicTopology.Products.CupCohomology.cohomologyCup (TopCat.toSSet.obj Y) p q
        (AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ p a) (AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ q b)) =
    AlgebraicTopology.Products.CupCohomology.cohomologyCup (TopCat.toSSet.obj X) p q
      (HomologicalComplex.homologyMap
        (AlgebraicTopology.Cohomology.Singular.Functor.simplicialPullback (ModuleCat.of ℚ ℚ) (TopCat.toSSet.map f)) p
        (AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ p a))
      (HomologicalComplex.homologyMap
        (AlgebraicTopology.Cohomology.Singular.Functor.simplicialPullback (ModuleCat.of ℚ ℚ) (TopCat.toSSet.map f)) q
        (AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ q b))
  rw [AlgebraicTopology.Products.CupCohomology.cohomologyCupWith_class_class, AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality.cochainClass_naturality,
    AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality.cochainClass_naturality, AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality.cochainClass_naturality, AlgebraicTopology.Products.CupCohomology.cohomologyCupWith_class_class]
  apply congrArg (AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ (p + q))
  apply Subtype.ext
  exact AlgebraicTopology.Products.Cup.cupWith_pullback (TopCat.toSSet.map f)
    (M := ModuleCat.of ℚ ℚ) (N := ModuleCat.of ℚ ℚ) (L := ModuleCat.of ℚ ℚ)
    (LinearMap.mul ℚ ℚ) a.val b.val

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Cohomology.Construction
