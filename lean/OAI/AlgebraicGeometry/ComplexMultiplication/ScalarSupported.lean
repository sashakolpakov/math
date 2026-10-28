import OAI.AlgebraicGeometry.ComplexMultiplication.ScalarClosedSupport
import OAI.AlgebraicGeometry.CycleClass.Geometric.SupportStalkVanishes

/-! # Scalar Supported -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.ScalarSupported

noncomputable section

/-! # Scalar comparison retains the actual support kernel complex -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace

variable (R : Type) [CommRing R] (Y : TopCat.{0})

local notation "G" => sheafCompose (Opens.grothendieckTopology Y)
  (forget₂ (ModuleCat R) AddCommGrpCat)
local notation "GN" => Functor.mapHomologicalComplex (G) (ComplexShape.up ℕ)
local notation "S" => OAI.AlgebraicTopology.Support.DerivedSections.TopCat.Sheaf.sheafSectionsSupportedOutside Y

set_option backward.isDefEq.respectTransparency false in
/-- Each actual kernel degree is identified by its actual inclusion. -/
def scalarSupportedComplexDegreeIso (O : Opens Y)
    (K : CochainComplex (TopCat.Sheaf (ModuleCat.{0} R) Y) ℕ) (n : ℕ) :
    (G).obj ((CycleClass.Geometric.SupportStalkVanishes.Cohomology.supportedSheafComplex O K).X n) ≅
      ((S) O).obj ((G).obj (K.X n)) :=
  (G).mapIso (CycleClass.Geometric.SupportStalkVanishes.Cohomology.supportedSheafComplexDegreeIso O K n) ≪≫
    ScalarClosedSupport.scalarClosedSupportIso R Y O (K.X n)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The degreewise comparison retains the original inclusion in all cochains. -/
theorem scalarSupportedComplexDegreeIso_inclusion (O : Opens Y)
    (K : CochainComplex (TopCat.Sheaf (ModuleCat.{0} R) Y) ℕ) (n : ℕ) :
    (scalarSupportedComplexDegreeIso R Y O K n).hom ≫
        (AlgebraicTopology.Support.DerivedSections.TopCat.Sheaf.sheafSectionsSupportedOutsideInclusion Y O).app ((G).obj (K.X n)) =
      (G).map ((CycleClass.Geometric.SupportStalkVanishes.Cohomology.supportedSheafComplexInclusion O K).f n) := by
  dsimp only [scalarSupportedComplexDegreeIso, Iso.trans_hom, Functor.mapIso_hom]
  rw [Category.assoc, ScalarClosedSupport.scalarClosedSupportIso_inclusion, ← Functor.map_comp,
    CycleClass.Geometric.SupportStalkVanishes.Cohomology.supportedSheafComplexDegreeIso_inclusion]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The comparison commutes with the actual singular coboundaries. -/
def scalarSupportedComplexIso (O : Opens Y)
    (K : CochainComplex (TopCat.Sheaf (ModuleCat.{0} R) Y) ℕ) :
    (GN).obj (CycleClass.Geometric.SupportStalkVanishes.Cohomology.supportedSheafComplex O K) ≅
      (((S) O).mapHomologicalComplex (ComplexShape.up ℕ)).obj ((GN).obj K) :=
  HomologicalComplex.Hom.isoOfComponents
    (scalarSupportedComplexDegreeIso R Y O K) (by
      intro i j hij
      apply (cancel_mono
        ((AlgebraicTopology.Support.DerivedSections.TopCat.Sheaf.sheafSectionsSupportedOutsideInclusion Y O).app
          ((G).obj (K.X j)))).mp
      symm
      change ((G).map ((CycleClass.Geometric.SupportStalkVanishes.Cohomology.supportedSheafComplex O K).d i j) ≫
          (scalarSupportedComplexDegreeIso R Y O K j).hom) ≫ _ =
        ((scalarSupportedComplexDegreeIso R Y O K i).hom ≫
          ((S) O).map ((G).map (K.d i j))) ≫ _
      rw [Category.assoc, scalarSupportedComplexDegreeIso_inclusion, Category.assoc,
        (AlgebraicTopology.Support.DerivedSections.TopCat.Sheaf.sheafSectionsSupportedOutsideInclusion Y O).naturality,
        ← Category.assoc, scalarSupportedComplexDegreeIso_inclusion,
        Functor.id_map, ← Functor.map_comp, ← Functor.map_comp]
      exact congrArg ((G).map)
        ((CycleClass.Geometric.SupportStalkVanishes.Cohomology.supportedSheafComplexInclusion O K).comm i j).symm)

end

end OAI.AlgebraicGeometry.ComplexMultiplication.ScalarSupported
