import OAI.AlgebraicTopology.Kunneth.ManifoldIntegrationCup
import OAI.AlgebraicTopology.DeRham.Comparison.Projective

/-! # Projective Cup Purity -/

namespace OAI.AlgebraicTopology.Kunneth.ProjectiveCupPurity

noncomputable section

/-! The actual projective Betti cup product preserves the specified pure Hodge types. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory

namespace Constructions

theorem simplicialCohomologyCup_pullback {K J : SSet.{0}} (f : K ⟶ J) (p q : ℕ)
    (a : (Cohomology.Singular.Basic.simplicialCochains J (ModuleCat.of ℂ ℂ)).homology p)
    (b : (Cohomology.Singular.Basic.simplicialCochains J (ModuleCat.of ℂ ℂ)).homology q) :
    HomologicalComplex.homologyMap (Cohomology.Singular.Functor.simplicialPullback (ModuleCat.of ℂ ℂ) f) (p + q)
      (Products.CupCohomology.cohomologyCup J p q a b) =
      Products.CupCohomology.cohomologyCup K p q
        (HomologicalComplex.homologyMap (Cohomology.Singular.Functor.simplicialPullback (ModuleCat.of ℂ ℂ) f) p a)
        (HomologicalComplex.homologyMap (Cohomology.Singular.Functor.simplicialPullback (ModuleCat.of ℂ ℂ) f) q b) := by
  obtain ⟨c, rfl⟩ := Cohomology.Singular.Representatives.cochainClass_surjective (Cohomology.Singular.Basic.simplicialCochains J (ModuleCat.of ℂ ℂ)) p a
  obtain ⟨d, rfl⟩ := Cohomology.Singular.Representatives.cochainClass_surjective (Cohomology.Singular.Basic.simplicialCochains J (ModuleCat.of ℂ ℂ)) q b
  rw [Products.CupCohomology.cohomologyCupWith_class_class, Cohomology.Singular.RepresentativesNaturality.cochainClass_naturality,
    Cohomology.Singular.RepresentativesNaturality.cochainClass_naturality, Cohomology.Singular.RepresentativesNaturality.cochainClass_naturality, Products.CupCohomology.cohomologyCupWith_class_class]
  apply congrArg (Cohomology.Singular.Representatives.cochainClass (Cohomology.Singular.Basic.simplicialCochains K (ModuleCat.of ℂ ℂ)) (p + q))
  apply Subtype.ext
  exact Products.Cup.cupWith_pullback f (L := ModuleCat.of ℂ ℂ) (LinearMap.mul ℂ ℂ) c.val d.val

def projectiveFormBettiClass (V : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (n : ℕ)
    (a : Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms V.analyticModel V.analyticSpace n) : V.complexCohomology n :=
  (V.deRhamBettiIso n).hom (V.deRhamClass n a)

theorem projectiveFormBettiClass_cast (V : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) {n m : ℕ} (h : n = m)
    (a : Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms V.analyticModel V.analyticSpace n) :
    projectiveFormBettiClass V m (ClosedManifoldWedge.Constructions.closedManifoldDegreeCast h a) =
      cast (congrArg (fun k => (V.complexCohomology k : Type)) h) (projectiveFormBettiClass V n a) := by
  subst m
  rfl

theorem bettiToSmoothSingular_cup (V : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (p q : ℕ)
    (a : V.complexCohomology p) (b : V.complexCohomology q) :
    V.bettiToSmoothSingular (p + q) (Products.CupCohomology.singularCohomologyCup (AlgebraicGeometry.Betti.Scheme.schemePointSpace V.toOver) p q a b) =
      Products.CupCohomology.cohomologyCup (Cohomology.Singular.ManifoldSmooth.manifoldSmoothSingularSubcomplex V.analyticModel V.analyticSpace).toSSet p q
        (V.bettiToSmoothSingular p a) (V.bettiToSmoothSingular q b) :=
  simplicialCohomologyCup_pullback
    (Cohomology.Singular.ManifoldSmooth.manifoldSmoothSingularSubcomplex V.analyticModel V.analyticSpace).ι p q a b

theorem projectiveFormBettiClass_wedge (V : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) {p q : ℕ}
    (a : Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms V.analyticModel V.analyticSpace p)
    (b : Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms V.analyticModel V.analyticSpace q) :
    projectiveFormBettiClass V (p + q) (ClosedManifoldWedge.Constructions.closedManifoldWedge a b) =
      Products.CupCohomology.singularCohomologyCup (AlgebraicGeometry.Betti.Scheme.schemePointSpace V.toOver) p q
        (projectiveFormBettiClass V p a) (projectiveFormBettiClass V q b) := by
  have : IsIso (V.bettiToSmoothSingular (p + q)) := by
    change IsIso (HomologicalComplex.homologyMap V.bettiRestrictionCochain (p + q))
    infer_instance
  apply (asIso (V.bettiToSmoothSingular (p + q))).toLinearEquiv.injective
  change V.bettiToSmoothSingular (p + q) (projectiveFormBettiClass V (p + q) (ClosedManifoldWedge.Constructions.closedManifoldWedge a b)) =
    V.bettiToSmoothSingular (p + q) (Products.CupCohomology.singularCohomologyCup (AlgebraicGeometry.Betti.Scheme.schemePointSpace V.toOver) p q
      (projectiveFormBettiClass V p a) (projectiveFormBettiClass V q b))
  rw [bettiToSmoothSingular_cup]
  unfold projectiveFormBettiClass
  rw [V.deRhamBettiIso_formClass, V.deRhamBettiIso_formClass, V.deRhamBettiIso_formClass]
  exact ManifoldIntegrationCup.Constructions.smoothSimplexIntegrationClass_wedge a b

theorem projectiveCup_mem_pure (V : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (p q r s : ℕ)
    (a : V.complexCohomology (p + q)) (b : V.complexCohomology (r + s))
    (ha : a ∈ V.pureBettiSubspace p q) (hb : b ∈ V.pureBettiSubspace r s) :
    cast (congrArg (fun k => (V.complexCohomology k : Type)) (add_add_add_comm p q r s))
      (Products.CupCohomology.singularCohomologyCup (AlgebraicGeometry.Betti.Scheme.schemePointSpace V.toOver) (p + q) (r + s) a b) ∈
        V.pureBettiSubspace (p + r) (q + s) := by
  obtain ⟨a', ha', hea⟩ := (V.mem_pureBettiSubspace_iff p q a).mp ha
  obtain ⟨b', hb', heb⟩ := (V.mem_pureBettiSubspace_iff r s b).mp hb
  apply (V.mem_pureBettiSubspace_iff (p + r) (q + s) _).mpr
  refine ⟨ClosedManifoldWedge.Constructions.closedManifoldDegreeCast (add_add_add_comm p q r s) (ClosedManifoldWedge.Constructions.closedManifoldWedge a' b'),
    ClosedManifoldWedge.Constructions.closedManifoldWedge_hasTangentBidegree a' b' ha' hb', ?_⟩
  change projectiveFormBettiClass V ((p + r) + (q + s))
    (ClosedManifoldWedge.Constructions.closedManifoldDegreeCast (add_add_add_comm p q r s) (ClosedManifoldWedge.Constructions.closedManifoldWedge a' b')) = _
  rw [projectiveFormBettiClass_cast, projectiveFormBettiClass_wedge]
  change projectiveFormBettiClass V (p + q) a' = a at hea
  change projectiveFormBettiClass V (r + s) b' = b at heb
  rw [hea, heb]

end Constructions

end

end OAI.AlgebraicTopology.Kunneth.ProjectiveCupPurity
