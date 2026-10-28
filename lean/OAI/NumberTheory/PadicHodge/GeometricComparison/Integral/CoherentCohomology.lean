import OAI.NumberTheory.PadicHodge.GeometricComparison.Integral.AdditiveSheafCohomology
import OAI.NumberTheory.PadicHodge.GeometricComparison.Integral.FunctionsSheaf
import OAI.NumberTheory.PadicHodge.GeometricComparison.ConstantSheaf
import OAI.AlgebraicGeometry.Crystalline.Cohomology.ProperCoherentCoefficient
import OAI.NumberTheory.PadicHodge.IntegralComparison.AlgebraSheafScalars

/-! # Coherent Cohomology -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Integral.CoherentCohomology.IntegralCoherentCohomology

noncomputable section

/-! The actual integral coefficient cohomology of scheme modules agrees with coherent cohomology, including its base action. -/

open _root_.CategoryTheory _root_.CategoryTheory.Abelian _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

open OAI.NumberTheory.PadicHodge.GeometricComparison.Integral.SheafCoefficientAdjunction.IntegralSheafCoefficientAdjunction OAI.NumberTheory.PadicHodge.GeometricComparison.Integral.IntegerSheafEquivalence.IntegralIntegerSheafEquivalence

variable (R : Type) [CommRing R] [Module.Flat ℤ R]
  (X : Over (Spec (CommRingCat.of R))) (M : X.left.Modules)

local notation "J" => Opens.grothendieckTopology X.left
local notation "V" => OAI.AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.Sheaves R X
local notation "F" => OAI.NumberTheory.PadicHodge.IntegralComparison.AlgebraSheafScalars.obj R X M

local instance : HasExt.{1} V := HasExt.standard _
local instance : HasExt.{0} (Sheaf J (ModuleCat ℤ)) := hasExt_of_enoughInjectives _
local instance : HasExt.{0} (Sheaf J AddCommGrpCat) := hasExt_of_enoughInjectives _

def underlyingIso : AdditiveSheafCohomology.IntegralAdditiveSheafCohomology.underlyingSheaf R J F ≅
    (SheafOfModules.toSheaf X.left.ringCatSheaf).obj M := Iso.refl _

def additiveEquiv (n : ℕ) :
    Ext.{1} (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.coefficientSheaf R X) F n ≃+ AlgebraicGeometry.SheafCohomology.AffineH.Projective.H M n :=
  (AdditiveSheafCohomology.IntegralAdditiveSheafCohomology.equiv R J F n).trans
    (((Sheaf.functorH J n).mapIso (underlyingIso R X M)).addCommGroupIsoToAddEquiv)

def baseScalar (r : R) : Γ(X.left, ⊤) :=
  X.hom.appTop ((Scheme.ΓSpecIso (CommRingCat.of R)).inv r)

omit [Module.Flat ℤ R] in
theorem baseScalar_eq (r : R) : baseScalar R X r = AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionBaseMap R X ⊤ r := by
  simp [baseScalar, AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionBaseMap, Scheme.Hom.appLE, Scheme.Hom.appTop]
  rfl

omit [Module.Flat ℤ R] in
theorem scalar_map (r : R) :
    (IntegerSheafEquivalence.IntegralIntegerSheafEquivalence.forgetSheaf J).map ((SheafCoefficientAdjunction.IntegralSheafCoefficientAdjunction.restrictSheaf R J).map (r • 𝟙 F)) ≫ (underlyingIso R X M).hom =
      (underlyingIso R X M).hom ≫ (SheafOfModules.toSheaf X.left.ringCatSheaf).map
        (AlgebraicGeometry.SheafCohomology.AffineH.Projective.globalSmulHom M (baseScalar R X r)) := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro x
  let y : M.val.obj U := x
  let : Module Γ(X.left, U.unop) (M.val.obj U) := (M.val.obj U).isModule
  change AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionBaseMap R X U.unop r • y =
    X.left.presheaf.map (homOfLE (show U.unop ≤ ⊤ from le_top)).op (baseScalar R X r) • y
  rw [baseScalar_eq, AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionBaseMap_naturality]

def linearEquiv (n : ℕ) :
    letI := IntegralComparison.Projective.CoherentFiniteness.coefficientModule R X.hom M n
    Ext.{1} (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.coefficientSheaf R X) F n ≃ₗ[R] AlgebraicGeometry.SheafCohomology.AffineH.Projective.H M n := by
  let := IntegralComparison.Projective.CoherentFiniteness.coefficientModule R X.hom M n
  refine { additiveEquiv R X M n with map_smul' := ?_ }
  intro r x
  rw [Ext.smul_eq_comp_mk₀]
  change Sheaf.H.map (underlyingIso R X M).hom n
      (AdditiveSheafCohomology.IntegralAdditiveSheafCohomology.equiv R J F n
        (x.comp (Ext.mk₀ (r • 𝟙 F)) (Nat.add_zero n))) = _
  erw [AdditiveSheafCohomology.IntegralAdditiveSheafCohomology.naturality]
  change Sheaf.H.map (underlyingIso R X M).hom n
    (Sheaf.H.map ((IntegerSheafEquivalence.IntegralIntegerSheafEquivalence.forgetSheaf J).map ((SheafCoefficientAdjunction.IntegralSheafCoefficientAdjunction.restrictSheaf R J).map (r • 𝟙 F))) n
      (AdditiveSheafCohomology.IntegralAdditiveSheafCohomology.equiv R J F n x)) =
    Sheaf.H.map ((SheafOfModules.toSheaf X.left.ringCatSheaf).map
      (AlgebraicGeometry.SheafCohomology.AffineH.Projective.globalSmulHom M (baseScalar R X r))) n (additiveEquiv R X M n x)
  rw [← Sheaf.H.map_comp_apply, scalar_map, Sheaf.H.map_comp_apply]
  rfl

theorem finite [M.IsQuasicoherent] [M.IsFiniteType] [IsNoetherianRing R] [IsProper X.hom] (n : ℕ) :
    Module.Finite R (Ext.{1} (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.coefficientSheaf R X) F n) := by
  let := IntegralComparison.Projective.CoherentFiniteness.coefficientModule R X.hom M n
  let := AlgebraicGeometry.Crystalline.Cohomology.ProperCoherentCoefficient.ProperCoherentFiniteness.coefficient R X.hom M n
  exact Module.Finite.equiv (linearEquiv R X M n).symm

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Integral.CoherentCohomology.IntegralCoherentCohomology
