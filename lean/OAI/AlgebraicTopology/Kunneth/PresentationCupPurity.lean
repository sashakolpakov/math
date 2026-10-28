import OAI.AlgebraicTopology.Kunneth.ProjectiveCupPurity
import OAI.AlgebraicTopology.Kunneth.PresentationPullbackPurity
import OAI.AlgebraicTopology.Kunneth.CupPullbackSingular

/-! # Presentation Cup Purity -/

namespace OAI.AlgebraicTopology.Kunneth.PresentationCupPurity

noncomputable section

/-! Cup and exterior-product Hodge purity, including empty and disconnected presentations. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory

namespace Constructions

theorem schemeBettiMap_degreeCast {X Y : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} (f : X ⟶ Y)
    {n m : ℕ} (h : n = m) (a : AlgebraicGeometry.Betti.Scheme.schemeBetti (ModuleCat.of ℂ ℂ) Y n) :
    AlgebraicGeometry.Betti.Scheme.schemeBettiMap (ModuleCat.of ℂ ℂ) m f
      (cast (congrArg (fun k => (AlgebraicGeometry.Betti.Scheme.schemeBetti (ModuleCat.of ℂ ℂ) Y k : Type)) h) a) =
      cast (congrArg (fun k => (AlgebraicGeometry.Betti.Scheme.schemeBetti (ModuleCat.of ℂ ℂ) X k : Type)) h)
        (AlgebraicGeometry.Betti.Scheme.schemeBettiMap (ModuleCat.of ℂ ℂ) n f a) := by
  subst m
  rfl

theorem schemeBettiMap_cup {X Y : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} (f : X ⟶ Y) (p q : ℕ)
    (a : AlgebraicGeometry.Betti.Scheme.schemeBetti (ModuleCat.of ℂ ℂ) Y p) (b : AlgebraicGeometry.Betti.Scheme.schemeBetti (ModuleCat.of ℂ ℂ) Y q) :
    AlgebraicGeometry.Betti.Scheme.schemeBettiMap (ModuleCat.of ℂ ℂ) (p + q) f
      (Products.CupCohomology.singularCohomologyCup (AlgebraicGeometry.Betti.Scheme.schemePointSpace Y) p q a b) =
      Products.CupCohomology.singularCohomologyCup (AlgebraicGeometry.Betti.Scheme.schemePointSpace X) p q
        (AlgebraicGeometry.Betti.Scheme.schemeBettiMap (ModuleCat.of ℂ ℂ) p f a) (AlgebraicGeometry.Betti.Scheme.schemeBettiMap (ModuleCat.of ℂ ℂ) q f b) :=
  CupPullbackSingular.Construction.CupPullback.singularCohomologyCup_pullback (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map f) p q a b

theorem presentationCup_mem_pure (P : AlgebraicGeometry.Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (p q r s : ℕ)
    (a : P.complexCohomology (p + q)) (b : P.complexCohomology (r + s))
    (ha : a ∈ P.pureBettiSubspace p q) (hb : b ∈ P.pureBettiSubspace r s) :
    cast (congrArg (fun k => (P.complexCohomology k : Type)) (add_add_add_comm p q r s))
      (Products.CupCohomology.singularCohomologyCup (AlgebraicGeometry.Betti.Scheme.schemePointSpace P.toOver) (p + q) (r + s) a b) ∈
        P.pureBettiSubspace (p + r) (q + s) := by
  apply (P.mem_pureBettiSubspace_iff (p + r) (q + s) _).mpr
  intro C
  have haC := (P.mem_pureBettiSubspace_iff p q a).mp ha C
  have hbC := (P.mem_pureBettiSubspace_iff r s b).mp hb C
  rw [P.componentBettiEquiv_apply] at haC hbC ⊢
  rw [schemeBettiMap_degreeCast (P.componentInclusionOver C) (add_add_add_comm p q r s),
    schemeBettiMap_cup]
  exact ProjectiveCupPurity.Constructions.projectiveCup_mem_pure (P.componentVariety C) p q r s _ _ haC hbC

theorem presentationExteriorProduct_mem_pure
    (X Y Z : AlgebraicGeometry.Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (πX : Z.toOver ⟶ X.toOver) (πY : Z.toOver ⟶ Y.toOver)
    (p q r s : ℕ) (a : X.complexCohomology (p + q)) (b : Y.complexCohomology (r + s))
    (ha : a ∈ X.pureBettiSubspace p q) (hb : b ∈ Y.pureBettiSubspace r s) :
    cast (congrArg (fun k => (Z.complexCohomology k : Type)) (add_add_add_comm p q r s))
      (Products.CupCohomology.singularCohomologyCup (AlgebraicGeometry.Betti.Scheme.schemePointSpace Z.toOver) (p + q) (r + s)
        (AlgebraicGeometry.Betti.Scheme.schemeBettiMap (ModuleCat.of ℂ ℂ) (p + q) πX a)
        (AlgebraicGeometry.Betti.Scheme.schemeBettiMap (ModuleCat.of ℂ ℂ) (r + s) πY b)) ∈
      Z.pureBettiSubspace (p + r) (q + s) :=
  presentationCup_mem_pure Z p q r s _ _
    (PresentationPullbackPurity.Constructions.presentationPullback_mem_pure Z X πX p q a ha)
    (PresentationPullbackPurity.Constructions.presentationPullback_mem_pure Z Y πY r s b hb)

end Constructions

end

end OAI.AlgebraicTopology.Kunneth.PresentationCupPurity
