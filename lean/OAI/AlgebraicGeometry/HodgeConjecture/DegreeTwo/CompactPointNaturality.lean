import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.CompactPointNormalization
import OAI.AlgebraicTopology.Duality.Poincare.CompactSupportHomeomorph
import OAI.AlgebraicGeometry.CycleClass.Geometric.ComplexLocalPurityNaturality

/-! # Compact Point Naturality -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.CompactPointNaturality.Constructions

noncomputable section

/-! Actual compact point classes commute with homeomorphisms and coordinates. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace
open OAI.AlgebraicGeometry.CycleClass.Geometric.ComplexLocalPurityNaturality.Cycles OAI.AlgebraicTopology.Duality.Poincare.CompactSupportHomeomorph

set_option backward.isDefEq.respectTransparency false

theorem moduleIso_hom_ne_zero {M N : ModuleCat.{0} ℚ} (e : M ≅ N) (a : M)
    (ha : a ≠ 0) : e.hom a ≠ 0 := by
  intro h
  have hi := congrArg e.inv h
  rw [Iso.hom_inv_id_apply, map_zero] at hi
  exact ha hi

def compactPointCohomologyι (X : TopCat.{0}) (x : X) (n : ℕ) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X ({x}ᶜ : Set X) n ⟶
      AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ) X n :=
  AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportCohomologyι (ModuleCat.of ℚ ℚ) X ⟨{x},isCompact_singleton⟩ n

theorem compactSupportHomeomorphStage_map {X Y : TopCat.{0}} (e : X ≃ₜ Y)
    (K : Compacts X) (L : Compacts Y) (h : e '' (K : Set X) = (L : Set Y))
    (hf : Set.MapsTo (TopCat.isoOfHomeo (X := X) (Y := Y) e).hom (K : Set X)ᶜ (L : Set Y)ᶜ) (n : ℕ) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (TopCat.isoOfHomeo (X := X) (Y := Y) e).hom hf n ≫
      AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportCohomologyι (ModuleCat.of ℚ ℚ) X K n =
    AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportCohomologyι (ModuleCat.of ℚ ℚ) Y L n ≫
      (AlgebraicTopology.Duality.Poincare.CompactSupportHomeomorph.compactSupportedCohomologyHomeomorphIso (ModuleCat.of ℚ ℚ) e n).hom := by
  have hL : Compacts.equiv e K = L := Compacts.ext h
  subst L
  exact (AlgebraicTopology.Duality.Poincare.CompactSupportHomeomorph.compactSupportedCohomologyHomeomorphIso_ι (ModuleCat.of ℚ ℚ) e K n).symm

theorem compactPointCohomologyι_degreeCast (X : TopCat.{0}) (x : X)
    {n m : ℕ} (h : n = m)
    (a : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X ({x}ᶜ : Set X) n) :
    eqToHom (congrArg (AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ) X) h)
      (compactPointCohomologyι X x n a) =
    compactPointCohomologyι X x m
      (eqToHom (congrArg (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X ({x}ᶜ : Set X)) h) a) := by
  subst m
  rfl

theorem compactSupportCohomologyι_supportCast (X : TopCat.{0}) (K L : Compacts X)
    (hKL : K = L) (A : Set X) (hK : A = (K : Set X)ᶜ) (hL : A = (L : Set X)ᶜ)
    (n : ℕ) (a : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X A n) :
    AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportCohomologyι (ModuleCat.of ℚ ℚ) X K n
      (eqToHom (congrArg (fun S => AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X S n) hK) a) =
    AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportCohomologyι (ModuleCat.of ℚ ℚ) X L n
      (eqToHom (congrArg (fun S => AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X S n) hL) a) := by
  subst L
  rfl

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem compactCoordinatePointClass (d : ℕ) (e : E ≃L[ℂ] (Fin d → ℂ)) :
    compactPointCohomologyι (TopCat.of E) 0 (2*d) (CycleClass.Geometric.ComplexLocalPurityNaturality.Cycles.complexCoordinateLocalClass e) =
    (AlgebraicTopology.Duality.Poincare.CompactSupportHomeomorph.compactSupportedCohomologyHomeomorphIso (ModuleCat.of ℚ ℚ)
      e.toHomeomorph (2*d)).hom (CompactPointNormalization.Constructions.compactPointDualClass d) := by
  have h := compactSupportHomeomorphStage_map (X := TopCat.of E) (Y := TopCat.of (Fin d → ℂ)) e.toHomeomorph
    ⟨{0},isCompact_singleton⟩ ⟨{0},isCompact_singleton⟩
    (by change e '' ({0} : Set E) = {0}; rw [Set.image_singleton, map_zero])
    (CycleClass.Geometric.FiniteComplexLocalPurity.Cycles.complexLinearEquiv_mapsTo_puncture e) (2*d)
  exact ConcreteCategory.congr_hom h (CycleClass.Geometric.RationalLocalPurity.Cycles.complexNormalRationalDualClass d)

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.CompactPointNaturality.Constructions
