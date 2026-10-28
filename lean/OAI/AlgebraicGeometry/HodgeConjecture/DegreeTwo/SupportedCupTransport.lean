import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.NormalPairThomProjection
import OAI.AlgebraicTopology.Duality.Poincare.CompactSupportHomeomorph

/-! # Supported Cup Transport -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.SupportedCupTransport.Constructions

noncomputable section

/-! Actual cup products commute with support identification and compact homeomorphism pullback. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace
open OAI.AlgebraicTopology.Duality.Poincare.CompactSupportHomeomorph

set_option backward.isDefEq.respectTransparency false

theorem relativeSupportTransport_rightCup (X : TopCat.{0}) {A B : Set X} (h : A=B)
    (p q : ℕ) (a : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X A p)
    (b : AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) X q) :
    eqToHom (congrArg (fun S => AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X S (p+q)) h)
      (CycleClass.Geometric.RelativeCupCohomology.Cycles.relativeAbsoluteCohomologyCup (R := ℚ) X A p q a b) =
    CycleClass.Geometric.RelativeCupCohomology.Cycles.relativeAbsoluteCohomologyCup (R := ℚ) X B p q
      (eqToHom (congrArg (fun S => AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X S p) h) a) b := by
  subst B
  rfl

theorem relativeDegreeCast_supportTransport (X : TopCat.{0}) {A B : Set X} (h : A=B)
    {p q : ℕ} (hpq : p=q) (a : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X A p) :
    CycleClass.Geometric.RelativeCupCohomology.Cycles.relativeCohomologyCast (ModuleCat.of ℚ ℚ) X B hpq
      (eqToHom (congrArg (fun S => AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X S p) h) a) =
    eqToHom (congrArg (fun S => AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X S q) h)
      (CycleClass.Geometric.RelativeCupCohomology.Cycles.relativeCohomologyCast (ModuleCat.of ℚ ℚ) X A hpq a) := by
  subst B
  subst q
  rfl

theorem compactHomeomorph_inverse_mapsTo {X Y : TopCat.{0}} (e : X ≃ₜ Y) (K : Compacts X) :
    Set.MapsTo (TopCat.isoOfHomeo e).inv (Compacts.equiv e K : Set Y)ᶜ (K : Set X)ᶜ := by
  intro y hy
  apply (AlgebraicTopology.Duality.Poincare.CompactSupportHomeomorph.compactHomeomorph_complement_iff e K (e.symm y)).mpr
  simpa only [e.apply_symm_apply] using hy

theorem compactHomeomorphStage_inv_eq_pullback {X Y : TopCat.{0}} (e : X ≃ₜ Y) (K : Compacts X) (n : ℕ) :
    (AlgebraicTopology.Duality.Poincare.CompactSupportHomeomorph.compactSupportHomeomorphStageCohomologyIso (ModuleCat.of ℚ ℚ) e K n).inv =
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (TopCat.isoOfHomeo e).inv
        (compactHomeomorph_inverse_mapsTo e K) n := rfl

theorem compactHomeomorphStage_inv_rightCup {X Y : TopCat.{0}} (e : X ≃ₜ Y) (K : Compacts X)
    (p q : ℕ) (a : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X (K : Set X)ᶜ p)
    (b : AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) X q) :
    (AlgebraicTopology.Duality.Poincare.CompactSupportHomeomorph.compactSupportHomeomorphStageCohomologyIso (ModuleCat.of ℚ ℚ) e K (p+q)).inv
      (CycleClass.Geometric.RelativeCupCohomology.Cycles.relativeAbsoluteCohomologyCup (R := ℚ) X (K : Set X)ᶜ p q a b) =
    CycleClass.Geometric.RelativeCupCohomology.Cycles.relativeAbsoluteCohomologyCup (R := ℚ) Y (Compacts.equiv e K : Set Y)ᶜ p q
      ((AlgebraicTopology.Duality.Poincare.CompactSupportHomeomorph.compactSupportHomeomorphStageCohomologyIso (ModuleCat.of ℚ ℚ) e K p).inv a)
      (AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of ℚ ℚ) (TopCat.isoOfHomeo e).inv q b) := by
  rw [compactHomeomorphStage_inv_eq_pullback, compactHomeomorphStage_inv_eq_pullback]
  exact CycleClass.Geometric.RelativeCupCohomology.Cycles.relativeAbsoluteCohomologyCupWith_pullback Y (Compacts.equiv e K : Set Y)ᶜ
    (M := ModuleCat.of ℚ ℚ) (N := ModuleCat.of ℚ ℚ) (L := ModuleCat.of ℚ ℚ)
    (LinearMap.mul ℚ ℚ) (TopCat.isoOfHomeo e).inv (compactHomeomorph_inverse_mapsTo e K) p q a b

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.SupportedCupTransport.Constructions
