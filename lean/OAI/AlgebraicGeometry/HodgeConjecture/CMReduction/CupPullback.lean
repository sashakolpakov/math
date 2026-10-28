import OAI.AlgebraicTopology.Products.CupCohomology
import OAI.AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality
import OAI.AlgebraicGeometry.Betti.Scheme

/-! # Cup Pullback -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMReduction.CupPullback.CM.Construction

noncomputable section

/-! Naturality of the actual cup product, proved from the cochain formula.
CMReduction uses this when pulling exterior products back along diagonals. -/

open _root_.CategoryTheory

open OAI.AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality OAI.AlgebraicTopology.Products.CupCohomology

theorem cup_pullback {R : Type} [CommRing R]
    {X Y : TopCat.{0}} (f : X ⟶ Y) (p q : ℕ)
    (a : AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of R R) Y p)
    (b : AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of R R) Y q) :
    AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of R R) f (p + q)
      (AlgebraicTopology.Products.CupCohomology.singularCohomologyCup Y p q a b) =
    AlgebraicTopology.Products.CupCohomology.singularCohomologyCup X p q
      (AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of R R) f p a)
      (AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of R R) f q b) := by
  obtain ⟨c, rfl⟩ := AlgebraicTopology.Cohomology.Singular.Representatives.singularClass_surjective (ModuleCat.of R R) Y p a
  obtain ⟨d, rfl⟩ := AlgebraicTopology.Cohomology.Singular.Representatives.singularClass_surjective (ModuleCat.of R R) Y q b
  rw [AlgebraicTopology.Products.CupCohomology.singularCohomologyCup_class_class, AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality.singularCohomologyPullback_class,
    AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality.singularCohomologyPullback_class, AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality.singularCohomologyPullback_class,
    AlgebraicTopology.Products.CupCohomology.singularCohomologyCup_class_class]
  apply congrArg (AlgebraicTopology.Cohomology.Singular.Representatives.singularClass (ModuleCat.of R R) X (p + q))
  apply Subtype.ext
  exact AlgebraicTopology.Products.Cup.cupWith_pullback (TopCat.toSSet.map f)
    (M := ModuleCat.of R R) (N := ModuleCat.of R R) (L := ModuleCat.of R R)
    (LinearMap.mul R R) c.val d.val

theorem scheme_cup_pullback {R : Type} [CommRing R]
    {X Y : CategoryTheory.Over Foundations.Scheme.ProjectiveSpace.complexBase} (f : X ⟶ Y) (p q : ℕ)
    (a : Betti.Scheme.schemeBetti (ModuleCat.of R R) Y p)
    (b : Betti.Scheme.schemeBetti (ModuleCat.of R R) Y q) :
    Betti.Scheme.schemeBettiMap (ModuleCat.of R R) (p + q) f
      (AlgebraicTopology.Products.CupCohomology.singularCohomologyCup (Betti.Scheme.schemePointSpace Y) p q a b) =
    AlgebraicTopology.Products.CupCohomology.singularCohomologyCup (Betti.Scheme.schemePointSpace X) p q
      (Betti.Scheme.schemeBettiMap (ModuleCat.of R R) p f a)
      (Betti.Scheme.schemeBettiMap (ModuleCat.of R R) q f b) :=
  cup_pullback (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map f) p q a b

theorem scheme_pullback_cast {R : Type} [CommRing R]
    {X Y : CategoryTheory.Over Foundations.Scheme.ProjectiveSpace.complexBase} (f : X ⟶ Y)
    {n m : ℕ} (h : n = m) (a : Betti.Scheme.schemeBetti (ModuleCat.of R R) Y n) :
    Betti.Scheme.schemeBettiMap (ModuleCat.of R R) m f
      (cast (congrArg (fun d => (Betti.Scheme.schemeBetti (ModuleCat.of R R) Y d : Type)) h) a) =
    cast (congrArg (fun d => (Betti.Scheme.schemeBetti (ModuleCat.of R R) X d : Type)) h)
      (Betti.Scheme.schemeBettiMap (ModuleCat.of R R) n f a) := by
  subst m
  rfl

theorem scheme_pullback_comp {R : Type} [CommRing R]
    {X Y Z : CategoryTheory.Over Foundations.Scheme.ProjectiveSpace.complexBase} (f : X ⟶ Y) (g : Y ⟶ Z)
    (n : ℕ) (a : Betti.Scheme.schemeBetti (ModuleCat.of R R) Z n) :
    Betti.Scheme.schemeBettiMap (ModuleCat.of R R) n f (Betti.Scheme.schemeBettiMap (ModuleCat.of R R) n g a) =
      Betti.Scheme.schemeBettiMap (ModuleCat.of R R) n (f ≫ g) a := by
  simp only [Betti.Scheme.schemeBettiMap, Functor.map_comp, AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback_comp,
    ConcreteCategory.comp_apply]

theorem scheme_pullback_id {R : Type} [CommRing R]
    (X : CategoryTheory.Over Foundations.Scheme.ProjectiveSpace.complexBase) (n : ℕ)
    (a : Betti.Scheme.schemeBetti (ModuleCat.of R R) X n) :
    Betti.Scheme.schemeBettiMap (ModuleCat.of R R) n (𝟙 X) a = a := by
  exact ConcreteCategory.congr_hom
    ((Betti.Scheme.schemeBettiFunctor (ModuleCat.of R R) n).map_id (Opposite.op X)) a

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMReduction.CupPullback.CM.Construction
