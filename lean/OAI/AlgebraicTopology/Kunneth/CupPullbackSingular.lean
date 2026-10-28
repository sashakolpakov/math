import OAI.AlgebraicTopology.Products.CupCohomology
import OAI.AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality

/-! # Cup Pullback Singular -/

namespace OAI.AlgebraicTopology.Kunneth.CupPullbackSingular

noncomputable section

/-! Naturality of the actual scalar cup product on cohomology. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory
open OAI.AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality OAI.AlgebraicTopology.Products.CupCohomology

namespace Construction.CupPullback

variable {R : Type} [CommRing R]

theorem singularCohomologyCup_pullback {X Y : TopCat.{0}} (f : X ⟶ Y) (p q : ℕ)
    (a : Cohomology.Singular.Basic.singularCohomology (ModuleCat.of R R) Y p)
    (b : Cohomology.Singular.Basic.singularCohomology (ModuleCat.of R R) Y q) :
    Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of R R) f (p + q)
      (Products.CupCohomology.singularCohomologyCup Y p q a b) =
      Products.CupCohomology.singularCohomologyCup X p q
        (Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of R R) f p a)
        (Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of R R) f q b) := by
  obtain ⟨c, rfl⟩ := Cohomology.Singular.Representatives.cochainClass_surjective (Cohomology.Singular.Basic.singularCochains (ModuleCat.of R R) Y) p a
  obtain ⟨d, rfl⟩ := Cohomology.Singular.Representatives.cochainClass_surjective (Cohomology.Singular.Basic.singularCochains (ModuleCat.of R R) Y) q b
  rw [Products.CupCohomology.singularCohomologyCup_class_class, Cohomology.Singular.RepresentativesNaturality.singularCohomologyPullback_class,
    Cohomology.Singular.RepresentativesNaturality.singularCohomologyPullback_class, Cohomology.Singular.RepresentativesNaturality.singularCohomologyPullback_class,
    Products.CupCohomology.singularCohomologyCup_class_class]
  apply congrArg (Cohomology.Singular.Representatives.singularClass (ModuleCat.of R R) X (p + q))
  apply Subtype.ext
  exact Products.Cup.cupWith_pullback (TopCat.toSSet.map f) (L := ModuleCat.of R R)
    (LinearMap.mul R R) c.val d.val

end Construction.CupPullback

end

end OAI.AlgebraicTopology.Kunneth.CupPullbackSingular
