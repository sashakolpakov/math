import OAI.AlgebraicGeometry.ComplexMultiplication.ScalarSupported
import OAI.AlgebraicTopology.Support.SingularFlasqueModel

/-! # Supported Singular Bridge -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.SupportedSingularBridge

noncomputable section

/-! # The actual singular support complexes agree under evaluation -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace

variable (R : Type) [CommRing R] (Y : TopCat.{0})

local notation "G" => sheafCompose (Opens.grothendieckTopology Y)
  (forget₂ (ModuleCat R) AddCommGrpCat)
local notation "GN" => Functor.mapHomologicalComplex (G) (ComplexShape.up ℕ)
local notation "S" => OAI.AlgebraicTopology.Support.DerivedSections.TopCat.Sheaf.sheafSectionsSupportedOutside Y
local notation "K" => OAI.AlgebraicTopology.Cohomology.Singular.SheafQuasiIso.sheafifiedCochainComplex
  (AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularPresheafComplex (ModuleCat.of R R) Y)
local notation "P" => OAI.AlgebraicTopology.Singular.SheafCochain.singularCochainSheafComplex R Y

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The full kernel-complex comparison retains inclusion into all cochains. -/
theorem scalarSupportedComplexIso_inclusion (O : Opens Y)
    (L : CochainComplex (TopCat.Sheaf (ModuleCat.{0} R) Y) ℕ) :
    (ScalarSupported.scalarSupportedComplexIso R Y O L).hom ≫
        ((AlgebraicTopology.Support.DerivedSections.TopCat.Sheaf.sheafSectionsSupportedOutsideInclusion Y O).mapHomologicalComplex
          (ComplexShape.up ℕ)).app ((GN).obj L) =
      (GN).map (CycleClass.Geometric.SupportStalkVanishes.Cohomology.supportedSheafComplexInclusion O L) := by
  apply HomologicalComplex.hom_ext
  intro n
  exact ScalarSupported.scalarSupportedComplexDegreeIso_inclusion R Y O L n

set_option backward.isDefEq.respectTransparency false in
/-- Actual chain evaluation identifies the supported singular complexes degree by degree. -/
def supportedSingularComplexBridgeIso (O : Opens Y) :
    (GN).obj (CycleClass.Geometric.SupportStalkVanishes.Cohomology.supportedSingularSheafComplex (ModuleCat.of R R) Y O) ≅
      ((S O).mapHomologicalComplex (ComplexShape.up ℕ)).obj (P) :=
  ScalarSupported.scalarSupportedComplexIso R Y O (K) ≪≫
    ((S O).mapHomologicalComplex (ComplexShape.up ℕ)).mapIso
      (SingularSheafBridge.singularSheafComplexBridgeIso R Y)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The supported comparison uses the unchanged ordinary singular comparison after inclusion. -/
theorem supportedSingularComplexBridgeIso_inclusion (O : Opens Y) :
    (supportedSingularComplexBridgeIso R Y O).hom ≫
        ((AlgebraicTopology.Support.DerivedSections.TopCat.Sheaf.sheafSectionsSupportedOutsideInclusion Y O).mapHomologicalComplex
          (ComplexShape.up ℕ)).app (P) =
      (GN).map (CycleClass.Geometric.SupportStalkVanishes.Cohomology.supportedSheafComplexInclusion O (K)) ≫
        (SingularSheafBridge.singularSheafComplexBridgeIso R Y).hom := by
  dsimp only [supportedSingularComplexBridgeIso, Iso.trans_hom, Functor.mapIso_hom]
  rw [Category.assoc,
    ((AlgebraicTopology.Support.DerivedSections.TopCat.Sheaf.sheafSectionsSupportedOutsideInclusion Y O).mapHomologicalComplex
      (ComplexShape.up ℕ)).naturality,
    ← Category.assoc, scalarSupportedComplexIso_inclusion]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Canonical extension by zero retains the full original integer-indexed support complex. -/
def supportedRationalSingularComplexIntBridgeIso (O : Opens Y) :
    (((sheafCompose (Opens.grothendieckTopology Y)
        (forget₂ (ModuleCat ℚ) AddCommGrpCat)).mapHomologicalComplex (ComplexShape.up ℕ)).obj
      (CycleClass.Geometric.SupportStalkVanishes.Cohomology.supportedSingularSheafComplex (ModuleCat.of ℚ ℚ) Y O)).extend
        ComplexShape.embeddingUpNat ≅
      AlgebraicTopology.Support.SingularFlasqueModel.Singular.supportedRationalSingularCochainComplex Y O :=
  (ComplexShape.embeddingUpNat.extendFunctor _).mapIso
      (supportedSingularComplexBridgeIso ℚ Y O) ≪≫
    (Algebra.Homology.MapExtend.HomologicalComplex.mapExtendCanonicalIso (S O)
      (AlgebraicTopology.Singular.SheafCochain.singularCochainSheafComplex ℚ Y)
      ComplexShape.embeddingUpNat).symm

end

end OAI.AlgebraicGeometry.ComplexMultiplication.SupportedSingularBridge
