import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.SmallFrame
import OAI.NumberTheory.PadicHodge.IntegralComparison.AffinePrincipal.Diagram
import OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallinePrincipal.Functor
import OAI.NumberTheory.PadicHodge.IntegralComparison.Small.PDComplexCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.Supported.PDComplex
import OAI.AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyTrans

/-! # Principal Frame -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalFrame

noncomputable section

/-! The original principal PD localizations map naturally to the
actual affine principal-open frames of a finite-level smooth model. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

abbrev Index (Z : Scheme.{0}) (V : Z.affineOpens) :=
  AlgebraicGeometry.Crystalline.Cohomology.PrincipalCoefficient.PrincipalCoefficientCategory.Object Γ(Z, V.val)

variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p]
  (n : ℕ) (X : Over (Spec (CommRingCat.of (Truncated.Witt.Ring p k n)))) [Smooth X.hom]
  (Y : Over (Spec (CommRingCat.of k))) (f : Y.left ⟶ X.left)
  (hp : IsPullback f Y.hom X.hom
    (Spec.map (CommRingCat.ofHom (Truncated.Witt.reduction p k n))))
  (U : X.left.affineOpens)

local notation "N" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.SmallFrame.functor p k n X Y f hp
local notation "Q" => Functor.obj N U
local notation "C" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalFrame.Index X.left U
local notation "F" => OAI.NumberTheory.PadicHodge.IntegralComparison.AffinePrincipal.Diagram.functor X.left U.val U.property

def frames := F ⋙ N

def projection (r : C) : (frames p k n X Y f hp U).obj r ⟶ Q :=
  (N).map (AffinePrincipal.Diagram.projection X.left U.val U.property r)

theorem projection_natural {r s : C} (a : r ⟶ s) :
    (frames p k n X Y f hp U).map a ≫ projection p k n X Y f hp U s =
      projection p k n X Y f hp U r := by
  change (N).map ((F).map a) ≫ (N).map _ = (N).map _
  rw [← CategoryTheory.Functor.map_comp, AffinePrincipal.Diagram.projection_natural]

theorem coefficient_unit (r : C) : IsUnit ((projection p k n X Y f hp U r).ambientMap r.val) := by
  have h := SmallFrame.map_ambient p k n X Y f hp
    (AffinePrincipal.Diagram.projection X.left U.val U.property r) r.val
  exact h.symm ▸ AffinePrincipal.Diagram.restricted_function_isUnit X.left U.val U.property r

def map (r : C) : (frames p k n X Y f hp U).obj r ⟶
    AlgebraicGeometry.Crystalline.Cohomology.CrystallinePrincipal.Functor.CrystallinePrincipalFunctor.object p k Y Q r :=
  AlgebraicGeometry.Crystalline.Cohomology.CrystallinePrincipal.Factorization.CrystallinePrincipalFactorization.lift p k Y (projection p k n X Y f hp U r) r.val
    (coefficient_unit p k n X Y f hp U r)

theorem map_projection (r : C) : PrincipalFrame.map p k n X Y f hp U r ≫
    AlgebraicGeometry.Crystalline.Cohomology.CrystallinePrincipal.Functor.CrystallinePrincipalFunctor.projection p k Y Q r = projection p k n X Y f hp U r :=
  AlgebraicGeometry.Crystalline.Cohomology.CrystallinePrincipal.Factorization.CrystallinePrincipalFactorization.lift_projection p k Y (projection p k n X Y f hp U r) r.val
    (coefficient_unit p k n X Y f hp U r)

def transformation : frames p k n X Y f hp U ⟶ AlgebraicGeometry.Crystalline.Cohomology.CrystallinePrincipal.Functor.CrystallinePrincipalFunctor.functor p k Y Q where
  app := PrincipalFrame.map p k n X Y f hp U
  naturality r s a := by
    apply (cancel_mono (AlgebraicGeometry.Crystalline.Cohomology.CrystallinePrincipal.Functor.CrystallinePrincipalFunctor.projection p k Y Q s)).mp
    rw [Category.assoc, map_projection, projection_natural, Category.assoc]
    exact ((congrArg (fun z => PrincipalFrame.map p k n X Y f hp U r ≫ z)
      (AlgebraicGeometry.Crystalline.Cohomology.CrystallinePrincipal.Functor.CrystallinePrincipalFunctor.map_projection p k Y Q a)).trans
        (map_projection p k n X Y f hp U r)).symm

def pdTransformation := Functor.whiskerRight (NatTrans.op (transformation p k n X Y f hp U))
  (Small.PDComplexCoordinates.originalFunctor p k Y)

def sourceIso : Supported.PDComplex.localizedComplex p k Y Q ≅
    AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly.complex (.up ℕ) ((AlgebraicGeometry.Crystalline.Cohomology.CrystallinePrincipal.Functor.CrystallinePrincipalFunctor.functor p k Y Q).op ⋙
      Small.PDComplexCoordinates.originalFunctor p k Y) :=
  ((Supported.PDComplex.restriction p k Y Q).mapHomologicalComplex (.up ℕ)).mapIso
      (Small.PDComplexCoordinates.originalAssemblyIso p k Y).symm ≪≫
    AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyTrans.ComplexAssemblyTransport.iso (AlgebraicGeometry.Crystalline.Cohomology.CrystallinePrincipal.Functor.CrystallinePrincipalFunctor.functor p k Y Q).op
      (𝟭 (ModuleCat (WittVector p k))) (.up ℕ) (Small.PDComplexCoordinates.originalFunctor p k Y)

def pdMap : Supported.PDComplex.localizedComplex p k Y Q ⟶
    AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly.complex (.up ℕ) ((frames p k n X Y f hp U).op ⋙
      Small.PDComplexCoordinates.originalFunctor p k Y) :=
  (sourceIso p k n X Y f hp U).hom ≫
    AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly.map (.up ℕ) (pdTransformation p k n X Y f hp U)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalFrame
