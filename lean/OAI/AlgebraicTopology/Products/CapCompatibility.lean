import OAI.AlgebraicTopology.Products.CapBoundary
import OAI.AlgebraicTopology.Products.CupCohomology

/-! # Cap Compatibility -/

namespace OAI.AlgebraicTopology.Products.CapCompatibility

noncomputable section

/-!
# Naturality and evaluation adjunction for the cap product

These identities concern the actual categorical (co)homology objects. They
follow from the checked chain-level formulas and the exact representative
formulas for the descended products.
-/

open _root_.CategoryTheory

variable {R : Type} [CommRing R]

/-- Naturality of the cap product on actual cycle representatives. -/
theorem capCycles_naturality {K L : SSet.{0}} (f : K ⟶ L) (p q : ℕ)
    (c : Cohomology.Singular.Representatives.cochainCocycles (Cohomology.Singular.Basic.simplicialCochains L (ModuleCat.of R R)) p)
    (z : Cohomology.Singular.ChainRepresentatives.chainCycles (Cohomology.Singular.ChainDual.simplicialScalarChains (R := R) K) (p + q)) :
    Cohomology.Singular.EvaluationNaturality.chainCycleMap (Cohomology.Singular.EvaluationNaturality.simplicialScalarChainMap (R := R) f) q
        (CapBoundary.capCycles K p q (Cohomology.Singular.RepresentativesNaturality.cochainCocycleMap (Cohomology.Singular.Functor.simplicialPullback (ModuleCat.of R R) f) p c) z) =
      CapBoundary.capCycles L p q c
        (Cohomology.Singular.EvaluationNaturality.chainCycleMap (Cohomology.Singular.EvaluationNaturality.simplicialScalarChainMap (R := R) f) (p + q) z) := by
  apply Subtype.ext
  exact LinearMap.congr_fun (Cap.cap_naturality f p q c.val) z.val

/-- Pushforward of the cap with a pulled-back class equals the cap of the
original class with the pushed-forward homology class. -/
theorem capHomology_naturality {K L : SSet.{0}} (f : K ⟶ L) (p q : ℕ)
    (c : (Cohomology.Singular.Basic.simplicialCochains L (ModuleCat.of R R)).homology p)
    (z : (Cohomology.Singular.ChainDual.simplicialScalarChains (R := R) K).homology (p + q)) :
    Cohomology.Singular.EvaluationNaturality.simplicialHomologyPushforward (R := R) f q
        (CapBoundary.capHomology K p q
          ((HomologicalComplex.homologyMap (Cohomology.Singular.Functor.simplicialPullback (ModuleCat.of R R) f) p) c) z) =
      CapBoundary.capHomology L p q c (Cohomology.Singular.EvaluationNaturality.simplicialHomologyPushforward (R := R) f (p + q) z) := by
  obtain ⟨c, rfl⟩ := Cohomology.Singular.Representatives.cochainClass_surjective (Cohomology.Singular.Basic.simplicialCochains L (ModuleCat.of R R)) p c
  obtain ⟨z, rfl⟩ := Cohomology.Singular.ChainRepresentatives.chainClass_surjective (Cohomology.Singular.ChainDual.simplicialScalarChains (R := R) K) (p + q) z
  rw [Cohomology.Singular.RepresentativesNaturality.cochainClass_naturality, CapBoundary.capHomology_class_class, Cohomology.Singular.EvaluationNaturality.chainClass_naturality,
    Cohomology.Singular.EvaluationNaturality.chainClass_naturality, CapBoundary.capHomology_class_class]
  exact congrArg (Cohomology.Singular.ChainRepresentatives.chainClass (Cohomology.Singular.ChainDual.simplicialScalarChains (R := R) L) q)
    (capCycles_naturality f p q c z)

/-- Naturality of the genuine singular cap product for continuous maps. -/
theorem singularCapHomology_naturality {X Y : TopCat.{0}} (f : X ⟶ Y) (p q : ℕ)
    (c : Cohomology.Singular.Basic.singularCohomology (ModuleCat.of R R) Y p)
    (z : (Cohomology.Singular.Evaluation.singularScalarChains (R := R) X).homology (p + q)) :
    Cohomology.Singular.EvaluationNaturality.singularHomologyPushforward (R := R) f q
        (CapBoundary.singularCapHomology X p q
          ((Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of R R) f p) c) z) =
      CapBoundary.singularCapHomology Y p q c (Cohomology.Singular.EvaluationNaturality.singularHomologyPushforward (R := R) f (p + q) z) :=
  capHomology_naturality (TopCat.toSSet.map f) p q c z

/-- Cup evaluation is adjoint to the cap product, with an arbitrary coefficient
module in the second cohomology argument. -/
theorem cohomologyCupWith_evaluation_cap (K : SSet.{0}) (M : ModuleCat.{0} R)
    (p q : ℕ) (c : (Cohomology.Singular.Basic.simplicialCochains K (ModuleCat.of R R)).homology p)
    (b : (Cohomology.Singular.Basic.simplicialCochains K M).homology q)
    (z : (Cohomology.Singular.ChainDual.simplicialScalarChains (R := R) K).homology (p + q)) :
    Cohomology.Singular.Evaluation.simplicialHomologyEvaluation K M (p + q)
        (CupCohomology.cohomologyCupWith K (M := ModuleCat.of R R) (N := M) (L := M)
          (LinearMap.lsmul R M) p q c b) z =
      Cohomology.Singular.Evaluation.simplicialHomologyEvaluation K M q b (CapBoundary.capHomology K p q c z) := by
  obtain ⟨c, rfl⟩ := Cohomology.Singular.Representatives.cochainClass_surjective (Cohomology.Singular.Basic.simplicialCochains K (ModuleCat.of R R)) p c
  obtain ⟨b, rfl⟩ := Cohomology.Singular.Representatives.cochainClass_surjective (Cohomology.Singular.Basic.simplicialCochains K M) q b
  obtain ⟨z, rfl⟩ := Cohomology.Singular.ChainRepresentatives.chainClass_surjective (Cohomology.Singular.ChainDual.simplicialScalarChains (R := R) K) (p + q) z
  rw [CupCohomology.cohomologyCupWith_class_class, CapBoundary.capHomology_class_class,
    Cohomology.Singular.Evaluation.simplicialHomologyEvaluation_class_class, Cohomology.Singular.Evaluation.simplicialHomologyEvaluation_class_class]
  exact CapBoundary.cap_cupWith_pairing K M c.val b.val z.val

/-- The scalar-coefficient cup-cap evaluation identity. -/
theorem cohomologyCup_evaluation_cap (K : SSet.{0}) (p q : ℕ)
    (c : (Cohomology.Singular.Basic.simplicialCochains K (ModuleCat.of R R)).homology p)
    (b : (Cohomology.Singular.Basic.simplicialCochains K (ModuleCat.of R R)).homology q)
    (z : (Cohomology.Singular.ChainDual.simplicialScalarChains (R := R) K).homology (p + q)) :
    Cohomology.Singular.Evaluation.simplicialHomologyEvaluation K (ModuleCat.of R R) (p + q)
        (CupCohomology.cohomologyCup K p q c b) z =
      Cohomology.Singular.Evaluation.simplicialHomologyEvaluation K (ModuleCat.of R R) q b (CapBoundary.capHomology K p q c z) := by
  have hmul : LinearMap.lsmul R R = LinearMap.mul R R := rfl
  simpa only [hmul] using cohomologyCupWith_evaluation_cap K (ModuleCat.of R R) p q c b z

/-- The cup-cap evaluation identity on genuine singular (co)homology, for
an arbitrary coefficient module. -/
theorem singularCupWith_evaluation_cap (X : TopCat.{0}) (M : ModuleCat.{0} R)
    (p q : ℕ) (c : Cohomology.Singular.Basic.singularCohomology (ModuleCat.of R R) X p)
    (b : Cohomology.Singular.Basic.singularCohomology M X q)
    (z : (Cohomology.Singular.Evaluation.singularScalarChains (R := R) X).homology (p + q)) :
    Cohomology.Singular.Evaluation.singularEvaluation M X (p + q)
        (CupCohomology.cohomologyCupWith (TopCat.toSSet.obj X) (M := ModuleCat.of R R) (N := M) (L := M)
          (LinearMap.lsmul R M) p q c b) z =
      Cohomology.Singular.Evaluation.singularEvaluation M X q b (CapBoundary.singularCapHomology X p q c z) :=
  cohomologyCupWith_evaluation_cap (TopCat.toSSet.obj X) M p q c b z

/-- The ordinary scalar singular cup product and cap product are adjoint
under the actual evaluation pairing. -/
theorem singularCohomologyCup_evaluation_cap (X : TopCat.{0}) (p q : ℕ)
    (c : Cohomology.Singular.Basic.singularCohomology (ModuleCat.of R R) X p)
    (b : Cohomology.Singular.Basic.singularCohomology (ModuleCat.of R R) X q)
    (z : (Cohomology.Singular.Evaluation.singularScalarChains (R := R) X).homology (p + q)) :
    Cohomology.Singular.Evaluation.singularEvaluation (ModuleCat.of R R) X (p + q)
        (CupCohomology.singularCohomologyCup X p q c b) z =
      Cohomology.Singular.Evaluation.singularEvaluation (ModuleCat.of R R) X q b (CapBoundary.singularCapHomology X p q c z) :=
  cohomologyCup_evaluation_cap (TopCat.toSSet.obj X) p q c b z

end

end OAI.AlgebraicTopology.Products.CapCompatibility
