import OAI.AlgebraicTopology.Cohomology.Singular.LocallyZeroCochains
import OAI.AlgebraicTopology.Cohomology.Singular.ParacompactSheafificationRepresentatives

/-! # Paracompact Comparison -/

namespace OAI.AlgebraicTopology.Cohomology.Singular.ParacompactComparison

noncomputable section

/-!
# Global singular comparison on paracompact Hausdorff spaces

Actual locally finite gluing proves that the canonical map from singular
cochains to global sections of their sheafification is degreewise surjective.
Its actual kernel is the proved acyclic complex of locally zero cochains,
giving a quasi-isomorphism over any characteristic-zero field.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite _root_.TopologicalSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {R : Type} [Ring R]

/-- The actual canonical map to sheafified global sections is degreewise
surjective on every paracompact Hausdorff space. -/
theorem singularCochainsToSheafSections_surjective_of_paracompact
    (M : ModuleCat.{0} R) (X : TopCat.{0}) [ParacompactSpace X] [T2Space X] (n : ℕ) :
    Function.Surjective ((LocallyZeroCochains.singularCochainsToSheafSections M X).f n) := by
  have htop : Function.Surjective
      ((Functor.singularPullback M (Opens.inclusion' (⊤ : Opens X))).f n) := by
    let e : Basic.singularCochains M X ≅ Basic.singularCochains M (TopCat.of (⊤ : Opens X)) :=
      (Functor.singularCochainsFunctor M).mapIso (Opens.inclusionTopIso X).op
    exact ((HomologicalComplex.eval (ModuleCat.{0} R)
      (ComplexShape.up ℕ) n).mapIso e).toLinearEquiv.surjective
  intro s
  obtain ⟨a, ha⟩ := ParacompactSheafificationRepresentatives.singularCochain_sheafification_top_surjective_of_paracompact M X n s
  obtain ⟨c, hc⟩ := htop a
  refine ⟨c, ?_⟩
  change (CategoryTheory.toSheafify (Opens.grothendieckTopology X)
    (DeRham.Comparison.SingularPresheaf.singularCochainDegreePresheaf M X n)).app (op ⊤)
      ((Functor.singularPullback M (Opens.inclusion' (⊤ : Opens X))).f n c) = s
  rw [hc]
  exact ha

/-- The actual singular-to-sheafified-sections map is a quasi-isomorphism
over a characteristic-zero field on a paracompact Hausdorff space. -/
theorem quasiIso_singularCochainsToSheafSections_of_paracompact
    (F : Type) [Field F] [CharZero F]
    (X : TopCat.{0}) [ParacompactSpace X] [T2Space X] :
    QuasiIso (LocallyZeroCochains.singularCochainsToSheafSections (ModuleCat.of F F) X) :=
  SurjectiveQuasiIso.quasiIso_of_surjective_of_acyclic_kernel
    (LocallyZeroCochains.singularCochainsToSheafSections (ModuleCat.of F F) X)
    (singularCochainsToSheafSections_surjective_of_paracompact (ModuleCat.of F F) X)
    (LocallyZeroCochains.locallyZeroSingularCochains_acyclic F X)

/-- The canonical global comparison of singular cohomology with the cohomology
of the actual sheafified-section complex on a paracompact Hausdorff space. -/
def paracompactSingularCohomologySheafSectionsIso
    (F : Type) [Field F] [CharZero F]
    (X : TopCat.{0}) [ParacompactSpace X] [T2Space X] (n : ℕ) :
    Basic.singularCohomology (ModuleCat.of F F) X n ≅
      (LocallyZeroCochains.singularSheafGlobalSections (ModuleCat.of F F) X).homology n := by
  have := quasiIso_singularCochainsToSheafSections_of_paracompact F X
  exact isoOfQuasiIsoAt (LocallyZeroCochains.singularCochainsToSheafSections (ModuleCat.of F F) X) n

/-- The comparison's forward map is induced by the actual canonical cochain
map, including the genuine sheafification unit. -/
@[simp]
theorem paracompactSingularCohomologySheafSectionsIso_hom
    (F : Type) [Field F] [CharZero F]
    (X : TopCat.{0}) [ParacompactSpace X] [T2Space X] (n : ℕ) :
    (paracompactSingularCohomologySheafSectionsIso F X n).hom =
      HomologicalComplex.homologyMap
        (LocallyZeroCochains.singularCochainsToSheafSections (ModuleCat.of F F) X) n := rfl

end

end OAI.AlgebraicTopology.Cohomology.Singular.ParacompactComparison
