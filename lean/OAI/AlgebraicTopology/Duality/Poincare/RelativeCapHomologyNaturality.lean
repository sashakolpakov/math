import OAI.AlgebraicTopology.Duality.Poincare.SupportRelativeCapHomology
import OAI.AlgebraicTopology.Duality.Poincare.SupportRelativeCapNaturality

/-! # Relative Cap Homology Naturality -/

namespace OAI.AlgebraicTopology.Duality.Poincare.RelativeCapHomologyNaturality

noncomputable section

/-!
# Naturality of the two-support cap product on relative (co)homology

Every map below is induced by the given continuous map of the two pairs.
The actual comparison from the small quotient to union-relative chains is
natural, so its proved inverse on homology is natural as well. This carries
the chain-level cap identity to the standard relative (co)homology groups.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {X Y : TopCat.{0}} (f : X ⟶ Y)
variable {A B : Set X} {A' B' : Set Y}
variable (hfA : Set.MapsTo f A A') (hfB : Set.MapsTo f B B')

/-- The finite two-support cap square restricts to the actual cycle modules. -/
theorem twoSupportSmallCapCycles_naturality (p q : ℕ)
    (c : Cohomology.Singular.Representatives.cochainCocycles (Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) Y A') p)
    (z : Cohomology.Singular.ChainRepresentatives.chainCycles (AlgebraicGeometry.CycleClass.Geometric.HomologyWithSupports.Cycles.binarySmallComplementChains X A B) (p + q)) :
    Cohomology.Singular.EvaluationNaturality.chainCycleMap (AlgebraicGeometry.CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainsMap ℚ f hfB) q
        (SupportRelativeCapHomology.twoSupportSmallCapCycles X A B p q
          (Cohomology.Singular.RepresentativesNaturality.cochainCocycleMap (Cohomology.Singular.RelativeSequence.relativeSingularCochainsMap (ModuleCat.of ℚ ℚ) f hfA) p c) z) =
      SupportRelativeCapHomology.twoSupportSmallCapCycles Y A' B' p q c
        (Cohomology.Singular.EvaluationNaturality.chainCycleMap (BinarySmallComplementFunctoriality.binarySmallComplementPairMap f hfA hfB) (p + q) z) := by
  apply Subtype.ext
  exact SupportRelativeCapNaturality.twoSupportSmallCap_naturality f hfA hfB p q c.val z.val

/-- The cap square descends to actual cohomology and the small-quotient homology. -/
theorem twoSupportSmallCapHomology_naturality (p q : ℕ)
    (c : Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) Y A' p)
    (z : (AlgebraicGeometry.CycleClass.Geometric.HomologyWithSupports.Cycles.binarySmallComplementChains X A B).homology (p + q)) :
    HomologicalComplex.homologyMap (AlgebraicGeometry.CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainsMap ℚ f hfB) q
        (SupportRelativeCapHomology.twoSupportSmallCapHomology X A B p q
          (Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) f hfA p c) z) =
      SupportRelativeCapHomology.twoSupportSmallCapHomology Y A' B' p q c
        (HomologicalComplex.homologyMap (BinarySmallComplementFunctoriality.binarySmallComplementPairMap f hfA hfB) (p + q) z) := by
  obtain ⟨c, rfl⟩ := Cohomology.Singular.Representatives.cochainClass_surjective
    (Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) Y A') p c
  obtain ⟨z, rfl⟩ := Cohomology.Singular.ChainRepresentatives.chainClass_surjective (AlgebraicGeometry.CycleClass.Geometric.HomologyWithSupports.Cycles.binarySmallComplementChains X A B) (p + q) z
  change HomologicalComplex.homologyMap (AlgebraicGeometry.CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainsMap ℚ f hfB) q
      (SupportRelativeCapHomology.twoSupportSmallCapHomology X A B p q
        (HomologicalComplex.homologyMap
          (Cohomology.Singular.RelativeSequence.relativeSingularCochainsMap (ModuleCat.of ℚ ℚ) f hfA) p
            (Cohomology.Singular.Representatives.cochainClass _ p c)) (Cohomology.Singular.ChainRepresentatives.chainClass _ (p + q) z)) =
    SupportRelativeCapHomology.twoSupportSmallCapHomology Y A' B' p q (Cohomology.Singular.Representatives.cochainClass _ p c)
      (HomologicalComplex.homologyMap (BinarySmallComplementFunctoriality.binarySmallComplementPairMap f hfA hfB) (p + q)
        (Cohomology.Singular.ChainRepresentatives.chainClass _ (p + q) z))
  rw [Cohomology.Singular.RepresentativesNaturality.cochainClass_naturality, SupportRelativeCapHomology.twoSupportSmallCapHomology_class_class,
    Cohomology.Singular.EvaluationNaturality.chainClass_naturality, Cohomology.Singular.EvaluationNaturality.chainClass_naturality, SupportRelativeCapHomology.twoSupportSmallCapHomology_class_class]
  exact congrArg (Cohomology.Singular.ChainRepresentatives.chainClass (AlgebraicGeometry.CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChains ℚ Y B') q)
    (twoSupportSmallCapCycles_naturality f hfA hfB p q c z)

/-- The homology comparison with the usual relative pair commutes with the
actual continuous map of the two support sets. -/
@[reassoc]
theorem binarySmallComplementHomologyIso_naturality
    (hA : IsOpen A) (hB : IsOpen B) (hA' : IsOpen A') (hB' : IsOpen B') (n : ℕ) :
    HomologicalComplex.homologyMap (BinarySmallComplementFunctoriality.binarySmallComplementPairMap f hfA hfB) n ≫
        (AlgebraicGeometry.CycleClass.Geometric.HomologyWithSupports.Cycles.binarySmallComplementHomologyIso Y A' B' hA' hB' n).hom =
      (AlgebraicGeometry.CycleClass.Geometric.HomologyWithSupports.Cycles.binarySmallComplementHomologyIso X A B hA hB n).hom ≫
        AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularHomologyMap f (hfA.union_union hfB) n := by
  change HomologicalComplex.homologyMap (BinarySmallComplementFunctoriality.binarySmallComplementPairMap f hfA hfB) n ≫
      HomologicalComplex.homologyMap (AlgebraicGeometry.CycleClass.Geometric.HomologyWithSupports.Cycles.binarySmallComplementToRelative Y A' B') n =
    HomologicalComplex.homologyMap (AlgebraicGeometry.CycleClass.Geometric.HomologyWithSupports.Cycles.binarySmallComplementToRelative X A B) n ≫
      HomologicalComplex.homologyMap (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChainsMap f (hfA.union_union hfB)) n
  rw [← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp,
    BinarySmallComplementFunctoriality.binarySmallComplementPairMap_toRelative]

/-- The genuine inverse comparison on relative homology is natural. -/
@[reassoc]
theorem binarySmallComplementHomologyIso_inv_naturality
    (hA : IsOpen A) (hB : IsOpen B) (hA' : IsOpen A') (hB' : IsOpen B') (n : ℕ) :
    (AlgebraicGeometry.CycleClass.Geometric.HomologyWithSupports.Cycles.binarySmallComplementHomologyIso X A B hA hB n).inv ≫
        HomologicalComplex.homologyMap (BinarySmallComplementFunctoriality.binarySmallComplementPairMap f hfA hfB) n =
      AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularHomologyMap f (hfA.union_union hfB) n ≫
        (AlgebraicGeometry.CycleClass.Geometric.HomologyWithSupports.Cycles.binarySmallComplementHomologyIso Y A' B' hA' hB' n).inv := by
  apply (cancel_mono (AlgebraicGeometry.CycleClass.Geometric.HomologyWithSupports.Cycles.binarySmallComplementHomologyIso Y A' B' hA' hB' n).hom).mp
  rw [Category.assoc, binarySmallComplementHomologyIso_naturality f hfA hfB hA hB hA' hB',
    Iso.inv_hom_id_assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- Naturality of the actual two-support relative cap product under any
continuous map carrying each support set into its specified target set. -/
theorem twoSupportRelativeCapHomology_naturality
    (hA : IsOpen A) (hB : IsOpen B) (hA' : IsOpen A') (hB' : IsOpen B') (p q : ℕ)
    (c : Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) Y A' p)
    (z : AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularHomology X (A ∪ B) (p + q)) :
    HomologicalComplex.homologyMap (AlgebraicGeometry.CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainsMap ℚ f hfB) q
        (SupportRelativeCapHomology.twoSupportRelativeCapHomology X A B hA hB p q
          (Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) f hfA p c) z) =
      SupportRelativeCapHomology.twoSupportRelativeCapHomology Y A' B' hA' hB' p q c
        (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularHomologyMap f (hfA.union_union hfB) (p + q) z) := by
  rw [SupportRelativeCapHomology.twoSupportRelativeCapHomology_apply, twoSupportSmallCapHomology_naturality,
    SupportRelativeCapHomology.twoSupportRelativeCapHomology_apply]
  exact congrArg (SupportRelativeCapHomology.twoSupportSmallCapHomology Y A' B' p q c)
    (ConcreteCategory.congr_hom
      (binarySmallComplementHomologyIso_inv_naturality f hfA hfB hA hB hA' hB' (p + q)) z)

end

end OAI.AlgebraicTopology.Duality.Poincare.RelativeCapHomologyNaturality
