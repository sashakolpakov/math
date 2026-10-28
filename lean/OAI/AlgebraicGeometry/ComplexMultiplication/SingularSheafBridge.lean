import OAI.AlgebraicGeometry.ComplexMultiplication.SingularPresheafBridge
import OAI.AlgebraicGeometry.ComplexMultiplication.ScalarForgettingSheafification
import OAI.AlgebraicTopology.Cohomology.Singular.SheafResolution

/-! # Singular Sheaf Bridge -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.SingularSheafBridge

noncomputable section

section

/-! # Evaluation identifies the actual singular sheaf complexes

The comparison sheafifies actual evaluation on chains and canonically forgets
module scalars. It retains the original topological space and coboundaries.
-/

open _root_.CategoryTheory _root_.TopologicalSpace

variable (R : Type) [CommRing R] (Y : TopCat.{0})

local notation "J" => Opens.grothendieckTopology Y
local notation "F" => forget₂ (ModuleCat R) AddCommGrpCat
local notation "K" => OAI.AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularPresheafComplex (ModuleCat.of R R) Y

/-- Forgetting scalars retains the actual sum of sheaf morphisms. -/
instance scalarSheafCompose_additive :
    (sheafCompose J (forget₂ (ModuleCat.{0} R) AddCommGrpCat.{0})).Additive where
  map_add := rfl

local instance complexScalarSheafCompose_additive :
    (sheafCompose J (forget₂ (ModuleCat.{0} ℂ) AddCommGrpCat.{0})).Additive where
  map_add := rfl

set_option backward.isDefEq.respectTransparency false in
/-- Actual chain evaluation, lifted through the canonical sheafification comparison. -/
def singularSheafComplexBridgeIso :
    (Functor.mapHomologicalComplex (sheafCompose J F) (ComplexShape.up ℕ)).obj
        (AlgebraicTopology.Cohomology.Singular.SheafQuasiIso.sheafifiedCochainComplex K) ≅
      AlgebraicTopology.Singular.SheafCochain.singularCochainSheafComplex R Y :=
  ((NatIso.mapHomologicalComplex (ScalarForgettingSheafification.scalarSheafificationCanonicalIso R Y)
      (ComplexShape.up ℕ)).app K).symm ≪≫
    ((presheafToSheaf J AddCommGrpCat).mapHomologicalComplex (ComplexShape.up ℕ)).mapIso
      (SingularPresheafBridge.singularPresheafComplexBridgeIso R Y)

/-- The comparison on the actual complex-coefficient singular sheaf complex. -/
def originalComplexSingularSheafBridgeIso :
    (Functor.mapHomologicalComplex
      (sheafCompose J (forget₂ (ModuleCat ℂ) AddCommGrpCat)) (ComplexShape.up ℕ)).obj
        (AlgebraicTopology.Cohomology.Singular.SheafResolution.singularSheafComplex Y) ≅
      AlgebraicTopology.Singular.SheafCochain.singularCochainSheafComplex ℂ Y :=
  singularSheafComplexBridgeIso ℂ Y

end

/-! # Actual singular evaluation commutes with sheafification units

The comparison is the proved chain evaluation and the canonical scalar
sheafification isomorphism, on the same open subspaces in every degree.
-/

open _root_.CategoryTheory _root_.TopologicalSpace

variable (R : Type) [CommRing R] (Y : TopCat.{0})

local notation "J" => Opens.grothendieckTopology Y
local notation "F" => forget₂ (ModuleCat R) AddCommGrpCat

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The inverse canonical comparison retains the same actual local sections. -/
theorem scalarSheafificationCanonicalIso_inv_unit
    (P : (Opens Y)ᵒᵖ ⥤ ModuleCat.{0} R) :
    Functor.whiskerRight (toSheafify J P) F ≫
        ((ScalarForgettingSheafification.scalarSheafificationCanonicalIso R Y).app P).inv.hom =
      toSheafify J (P ⋙ F) := by
  rw [← ScalarForgettingSheafification.scalarSheafificationCanonicalIso_unit R Y P, Category.assoc]
  have h : ((ScalarForgettingSheafification.scalarSheafificationCanonicalIso R Y).app P).hom.hom ≫
      ((ScalarForgettingSheafification.scalarSheafificationCanonicalIso R Y).app P).inv.hom = 𝟙 _ :=
    congrArg (fun f => f.hom)
      (((ScalarForgettingSheafification.scalarSheafificationCanonicalIso R Y).app P).hom_inv_id)
  rw [h]
  exact Category.comp_id _

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The actual singular sheaf-complex bridge agrees with evaluation on local cochains. -/
theorem singularSheafComplexBridgeIso_unit (n : ℕ) :
    Functor.whiskerRight
        (toSheafify J
          (AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularCochainDegreePresheaf (ModuleCat.of R R) Y n)) F ≫
        ((singularSheafComplexBridgeIso R Y).hom.f n).hom =
      (SingularPresheafBridge.singularCochainDegreePresheafBridgeIso R Y n).hom ≫
        toSheafify J (AlgebraicTopology.Singular.SheafCochain.singularCochainPresheaf R Y n) := by
  change Functor.whiskerRight (toSheafify J _) F ≫
      (((ScalarForgettingSheafification.scalarSheafificationCanonicalIso R Y).app
          (AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularCochainDegreePresheaf (ModuleCat.of R R) Y n)).inv.hom ≫
        ((presheafToSheaf J AddCommGrpCat).map
          (SingularPresheafBridge.singularCochainDegreePresheafBridgeIso R Y n).hom).hom) = _
  rw [← Category.assoc, scalarSheafificationCanonicalIso_inv_unit,
    ← toSheafify_naturality J (SingularPresheafBridge.singularCochainDegreePresheafBridgeIso R Y n).hom]

end

end OAI.AlgebraicGeometry.ComplexMultiplication.SingularSheafBridge
