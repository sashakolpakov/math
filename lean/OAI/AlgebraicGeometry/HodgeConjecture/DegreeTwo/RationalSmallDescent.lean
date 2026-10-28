import OAI.AlgebraicGeometry.CycleClass.Geometric.HomologyWithSupports
import OAI.AlgebraicGeometry.CycleClass.Geometric.RationalRelativeHomology

/-! # Rational Small Descent -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.RationalSmallDescent.Constructions

noncomputable section

section

/-!
# DegreeTwo: rational quotient by the actual binary-small chains

This is the exact rationalization of the established integral small-chain
quotient. Its comparison with ordinary relative homology is induced by
the proved subdivision comparison, with the actual quotient maps retained.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

set_option backward.isDefEq.respectTransparency false

variable (X : TopCat.{0}) (A B : Set X)

abbrev binaryRationalComplementChains : ChainComplex (ModuleCat.{0} ℚ) ℕ :=
  CycleClass.Geometric.RationalRelativeHomology.Cycles.rationalizeChains.obj (CycleClass.Geometric.HomologyWithSupports.Cycles.binarySmallComplementChains X A B)

def binaryRationalComplementProjection :
    AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) X ⟶ binaryRationalComplementChains X A B :=
  (CycleClass.Geometric.RationalSingularChains.Cycles.rationalSingularChainsIso X).inv ≫
    CycleClass.Geometric.RationalRelativeHomology.Cycles.rationalizeChains.map (CycleClass.Geometric.HomologyWithSupports.Cycles.binarySmallComplementProjection X A B)

instance binaryRationalComplementProjection_epi : Epi (binaryRationalComplementProjection X A B) := by
  unfold binaryRationalComplementProjection
  infer_instance

theorem binaryRationalComplementProjection_left :
    CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSubspaceChainInclusion ℚ X A ≫ binaryRationalComplementProjection X A B = 0 := by
  apply (cancel_epi (CycleClass.Geometric.RationalSingularChains.Cycles.rationalSingularChainsIso (TopCat.of A)).hom).mp
  rw [binaryRationalComplementProjection, ← Category.assoc,
    ← CycleClass.Geometric.RationalSingularChains.Cycles.rationalSingularChainsIso_hom_naturality, Category.assoc, Iso.hom_inv_id_assoc,
    ← CycleClass.Geometric.RationalRelativeHomology.Cycles.rationalizeChains.map_comp, CycleClass.Geometric.HomologyWithSupports.Cycles.subspaceChainInclusion_binarySmallComplement_left,
    CycleClass.Geometric.RationalRelativeHomology.Cycles.rationalizeChains.map_zero, comp_zero]

theorem binaryRationalComplementProjection_right :
    CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSubspaceChainInclusion ℚ X B ≫ binaryRationalComplementProjection X A B = 0 := by
  apply (cancel_epi (CycleClass.Geometric.RationalSingularChains.Cycles.rationalSingularChainsIso (TopCat.of B)).hom).mp
  rw [binaryRationalComplementProjection, ← Category.assoc,
    ← CycleClass.Geometric.RationalSingularChains.Cycles.rationalSingularChainsIso_hom_naturality, Category.assoc, Iso.hom_inv_id_assoc,
    ← CycleClass.Geometric.RationalRelativeHomology.Cycles.rationalizeChains.map_comp, CycleClass.Geometric.HomologyWithSupports.Cycles.subspaceChainInclusion_binarySmallComplement_right,
    CycleClass.Geometric.RationalRelativeHomology.Cycles.rationalizeChains.map_zero, comp_zero]

def binaryRationalComplementToRelative :
    binaryRationalComplementChains X A B ⟶ CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChains ℚ X (A ∪ B) :=
  CycleClass.Geometric.RationalRelativeHomology.Cycles.rationalizeChains.map (CycleClass.Geometric.HomologyWithSupports.Cycles.binarySmallComplementToRelative X A B) ≫
    (CycleClass.Geometric.RationalRelativeHomology.Cycles.rationalRelativeChainsIso X (A ∪ B)).hom

theorem binaryRationalComplementToRelative_projection :
    binaryRationalComplementProjection X A B ≫ binaryRationalComplementToRelative X A B =
      CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainProjection ℚ X (A ∪ B) := by
  rw [binaryRationalComplementProjection, binaryRationalComplementToRelative,
    Category.assoc, ← Category.assoc (CycleClass.Geometric.RationalRelativeHomology.Cycles.rationalizeChains.map _),
    ← CycleClass.Geometric.RationalRelativeHomology.Cycles.rationalizeChains.map_comp, CycleClass.Geometric.HomologyWithSupports.Cycles.binarySmallComplementToRelative_projection,
    CycleClass.Geometric.RationalRelativeHomology.Cycles.rationalRelativeChainsIso_projection, Iso.inv_hom_id_assoc]

theorem binaryRationalComplementToRelative_quasiIso (hA : IsOpen A) (hB : IsOpen B) :
    _root_.QuasiIso (binaryRationalComplementToRelative X A B) := by
  have := CycleClass.Geometric.HomologyWithSupports.Cycles.binarySmallComplementToRelative_quasiIso X A B hA hB
  unfold binaryRationalComplementToRelative
  infer_instance

def binaryRationalComplementHomologyIso (hA : IsOpen A) (hB : IsOpen B) (n : ℕ) :
    (binaryRationalComplementChains X A B).homology n ≅
      CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarHomology ℚ X (A ∪ B) n := by
  have := binaryRationalComplementToRelative_quasiIso X A B hA hB
  exact isoOfQuasiIsoAt (binaryRationalComplementToRelative X A B) n

end

section

/-!
# DegreeTwo: descend an actual chain map through the small-support quotient

A map annihilating both subspace chain complexes annihilates their
binary-small sum. The proof uses the actual Mayer–Vietoris epimorphism,
and descent uses the actual rationalized cokernel.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

set_option backward.isDefEq.respectTransparency false

variable (X : TopCat.{0}) (A B : Set X)
variable {E : ChainComplex (ModuleCat.{0} ℚ) ℕ} (f : AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) X ⟶ E)
variable (hA : CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSubspaceChainInclusion ℚ X A ≫ f = 0)
variable (hB : CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSubspaceChainInclusion ℚ X B ≫ f = 0)

include hA hB in
theorem rationalBinarySmallInclusion_zero :
    CycleClass.Geometric.RationalRelativeHomology.Cycles.rationalizeChains.map (CycleClass.Geometric.BinarySmallInclusion.Cycles.binarySmallIntegralChainInclusion X A B) ≫
      (CycleClass.Geometric.RationalSingularChains.Cycles.rationalSingularChainsIso X).hom ≫ f = 0 := by
  have : Epi (CycleClass.Geometric.SmallMayerVietoris.Cycles.smallMayerVietorisSequence X A B).g :=
    (CycleClass.Geometric.SmallMayerVietoris.Cycles.smallMayerVietorisSequence_shortExact X A B).epi_g
  let : PreservesBinaryBiproduct (CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains (TopCat.of A))
      (CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains (TopCat.of B)) CycleClass.Geometric.RationalRelativeHomology.Cycles.rationalizeChains :=
    preservesBinaryBiproduct_of_preservesBiproduct CycleClass.Geometric.RationalRelativeHomology.Cycles.rationalizeChains _ _
  apply (cancel_epi (CycleClass.Geometric.RationalRelativeHomology.Cycles.rationalizeChains.map (CycleClass.Geometric.SmallMayerVietoris.Cycles.smallMayerVietorisSequence X A B).g)).mp
  apply (cancel_epi (CycleClass.Geometric.RationalRelativeHomology.Cycles.rationalizeChains.mapBiprod
    (CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains (TopCat.of A)) (CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains (TopCat.of B))).inv).mp
  rw [Functor.mapBiprod_inv]
  apply biprod.hom_ext'
  · rw [biprod.inl_desc_assoc, ← CycleClass.Geometric.RationalRelativeHomology.Cycles.rationalizeChains.map_comp_assoc,
      CycleClass.Geometric.SmallMayerVietoris.Cycles.smallMayerVietorisSequence_g, biprod.inl_desc,
      ← CycleClass.Geometric.RationalRelativeHomology.Cycles.rationalizeChains.map_comp_assoc, CycleClass.Geometric.BinarySmallInclusion.Cycles.binarySmallIntegralChainInclusion_left,
      CycleClass.Geometric.RationalSingularChains.Cycles.rationalSingularChainsIso_hom_naturality_assoc, hA]
    simp only [comp_zero]
  · rw [biprod.inr_desc_assoc, ← CycleClass.Geometric.RationalRelativeHomology.Cycles.rationalizeChains.map_comp_assoc,
      CycleClass.Geometric.SmallMayerVietoris.Cycles.smallMayerVietorisSequence_g, biprod.inr_desc,
      ← CycleClass.Geometric.RationalRelativeHomology.Cycles.rationalizeChains.map_comp_assoc, CycleClass.Geometric.BinarySmallInclusion.Cycles.binarySmallIntegralChainInclusion_right,
      CycleClass.Geometric.RationalSingularChains.Cycles.rationalSingularChainsIso_hom_naturality_assoc, hB]
    simp only [comp_zero]

def binaryRationalComplementDesc : binaryRationalComplementChains X A B ⟶ E :=
  (PreservesCokernel.iso CycleClass.Geometric.RationalRelativeHomology.Cycles.rationalizeChains (CycleClass.Geometric.BinarySmallInclusion.Cycles.binarySmallIntegralChainInclusion X A B)).hom ≫
    cokernel.desc (CycleClass.Geometric.RationalRelativeHomology.Cycles.rationalizeChains.map (CycleClass.Geometric.BinarySmallInclusion.Cycles.binarySmallIntegralChainInclusion X A B))
      ((CycleClass.Geometric.RationalSingularChains.Cycles.rationalSingularChainsIso X).hom ≫ f) (rationalBinarySmallInclusion_zero X A B f hA hB)

theorem binaryRationalComplementDesc_projection :
    binaryRationalComplementProjection X A B ≫ binaryRationalComplementDesc X A B f hA hB = f := by
  rw [binaryRationalComplementProjection, binaryRationalComplementDesc, Category.assoc,
    ← Category.assoc (CycleClass.Geometric.RationalRelativeHomology.Cycles.rationalizeChains.map _), PreservesCokernel.π_iso_hom,
    cokernel.π_desc, Iso.inv_hom_id_assoc]

end

/-! The genuine small-support quotient universal property in a single chain degree. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

set_option backward.isDefEq.respectTransparency false

abbrev rationalChainDegree (n : ℕ) : ChainComplex (ModuleCat.{0} ℤ) ℕ ⥤ ModuleCat.{0} ℚ :=
  CycleClass.Geometric.RationalRelativeHomology.Cycles.rationalizeChains ⋙ HomologicalComplex.eval (ModuleCat.{0} ℚ) (ComplexShape.down ℕ) n

variable (X : TopCat.{0}) (A B : Set X) (n : ℕ)
variable {M : ModuleCat.{0} ℚ} (f : (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) X).X n ⟶ M)
variable (hA : (CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSubspaceChainInclusion ℚ X A).f n ≫ f = 0)
variable (hB : (CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSubspaceChainInclusion ℚ X B).f n ≫ f = 0)

include hA hB in
theorem rationalBinarySmallDegreeInclusion_zero :
    (rationalChainDegree n).map (CycleClass.Geometric.BinarySmallInclusion.Cycles.binarySmallIntegralChainInclusion X A B) ≫
      (CycleClass.Geometric.RationalSingularChains.Cycles.rationalSingularChainsIso X).hom.f n ≫ f = 0 := by
  let F := rationalChainDegree n
  have : Epi (CycleClass.Geometric.SmallMayerVietoris.Cycles.smallMayerVietorisSequence X A B).g :=
    (CycleClass.Geometric.SmallMayerVietoris.Cycles.smallMayerVietorisSequence_shortExact X A B).epi_g
  let : PreservesBinaryBiproduct (CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains (TopCat.of A))
      (CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains (TopCat.of B)) F :=
    preservesBinaryBiproduct_of_preservesBiproduct F _ _
  have hn (U : Set X) : F.map (CycleClass.Geometric.LocalHomology.Cycles.subspaceChainInclusion X U) ≫
      (CycleClass.Geometric.RationalSingularChains.Cycles.rationalSingularChainsIso X).hom.f n =
      (CycleClass.Geometric.RationalSingularChains.Cycles.rationalSingularChainsIso (TopCat.of U)).hom.f n ≫
        (CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSubspaceChainInclusion ℚ X U).f n :=
    HomologicalComplex.congr_hom (CycleClass.Geometric.RationalSingularChains.Cycles.rationalSingularChainsIso_hom_naturality (CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion X U)) n
  apply (cancel_epi (F.map (CycleClass.Geometric.SmallMayerVietoris.Cycles.smallMayerVietorisSequence X A B).g)).mp
  apply (cancel_epi (F.mapBiprod
    (CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains (TopCat.of A)) (CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains (TopCat.of B))).inv).mp
  rw [Functor.mapBiprod_inv]
  apply biprod.hom_ext'
  · rw [biprod.inl_desc_assoc, ← F.map_comp_assoc,
      CycleClass.Geometric.SmallMayerVietoris.Cycles.smallMayerVietorisSequence_g, biprod.inl_desc, ← F.map_comp_assoc,
      CycleClass.Geometric.BinarySmallInclusion.Cycles.binarySmallIntegralChainInclusion_left, ← Category.assoc, hn A, Category.assoc, hA]
    simp only [comp_zero]
  · rw [biprod.inr_desc_assoc, ← F.map_comp_assoc,
      CycleClass.Geometric.SmallMayerVietoris.Cycles.smallMayerVietorisSequence_g, biprod.inr_desc, ← F.map_comp_assoc,
      CycleClass.Geometric.BinarySmallInclusion.Cycles.binarySmallIntegralChainInclusion_right, ← Category.assoc, hn B, Category.assoc, hB]
    simp only [comp_zero]

def binaryRationalComplementDegreeDesc : (binaryRationalComplementChains X A B).X n ⟶ M :=
  (PreservesCokernel.iso (rationalChainDegree n) (CycleClass.Geometric.BinarySmallInclusion.Cycles.binarySmallIntegralChainInclusion X A B)).hom ≫
    cokernel.desc ((rationalChainDegree n).map (CycleClass.Geometric.BinarySmallInclusion.Cycles.binarySmallIntegralChainInclusion X A B))
      ((CycleClass.Geometric.RationalSingularChains.Cycles.rationalSingularChainsIso X).hom.f n ≫ f)
      (rationalBinarySmallDegreeInclusion_zero X A B n f hA hB)

theorem binaryRationalComplementDegreeDesc_projection :
    (binaryRationalComplementProjection X A B).f n ≫
      binaryRationalComplementDegreeDesc X A B n f hA hB = f := by
  change (CycleClass.Geometric.RationalSingularChains.Cycles.rationalSingularChainsIso X).inv.f n ≫
    (rationalChainDegree n).map (CycleClass.Geometric.HomologyWithSupports.Cycles.binarySmallComplementProjection X A B) ≫
    binaryRationalComplementDegreeDesc X A B n f hA hB = f
  rw [binaryRationalComplementDegreeDesc, ← Category.assoc ((rationalChainDegree n).map _),
    PreservesCokernel.π_iso_hom, cokernel.π_desc, ← Category.assoc]
  have hi : (CycleClass.Geometric.RationalSingularChains.Cycles.rationalSingularChainsIso X).inv.f n ≫ (CycleClass.Geometric.RationalSingularChains.Cycles.rationalSingularChainsIso X).hom.f n = 𝟙 _ :=
    HomologicalComplex.congr_hom (CycleClass.Geometric.RationalSingularChains.Cycles.rationalSingularChainsIso X).inv_hom_id n
  rw [hi, Category.id_comp]

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.RationalSmallDescent.Constructions
