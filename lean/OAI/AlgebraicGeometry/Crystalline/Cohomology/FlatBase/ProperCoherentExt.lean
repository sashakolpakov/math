import OAI.AlgebraicGeometry.Crystalline.Cohomology.FlatBase.BaseSheafCohomology
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Base.ModuleCoefficientPresheaf
import OAI.AlgebraicGeometry.Crystalline.Cohomology.ProperCoherentCoefficient
import OAI.AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId
import OAI.NumberTheory.PadicHodge.IntegralComparison.Module.SheafUniverses

/-! # Proper Coherent Ext -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.FlatBase.ProperCoherentExt.FlatBaseProperCoherentExt

noncomputable section

/-! # Proper coherent finiteness in the original flat-base coefficient Ext groups -/

open _root_.CategoryTheory _root_.CategoryTheory.Abelian _root_.AlgebraicGeometry

universe u

variable (k : Type u) [CommRing k] [Module.Flat ℤ k] (X : Over (Spec (CommRingCat.of k)))

local notation "J" => Opens.grothendieckTopology X.left
abbrev IntegerRing : Type u := SheafCoefficients.FlatBaseSheafCoefficients.Integers.{u}

local instance integerSheafify : HasSheafify J (ModuleCat.{u} IntegerRing.{u}) :=
  NumberTheory.PadicHodge.IntegralComparison.Module.SheafUniverses.hasSheafify.{u, u, u} J IntegerRing.{u}

local instance integerInjectives : EnoughInjectives (Sheaf J (ModuleCat.{u} IntegerRing.{u})) :=
  NumberTheory.PadicHodge.IntegralComparison.Module.SheafUniverses.enoughInjectives.{u, u, u} J IntegerRing.{u}

local instance coefficientInjectives : EnoughInjectives (DeRhamGlobalId.DeRhamGlobal.Sheaves k X) :=
  NumberTheory.PadicHodge.IntegralComparison.Module.SheafUniverses.enoughInjectives.{u, u, u} J k

local instance integerExt : HasExt.{u + 1} (Sheaf J (ModuleCat.{u} IntegerRing.{u})) := HasExt.standard _

local instance coefficientExt : HasExt.{u + 1} (DeRhamGlobalId.DeRhamGlobal.Sheaves k X) := HasExt.standard _

abbrev sheaf (M : X.left.Modules) := (NumberTheory.PadicHodge.IntegralComparison.AlgebraSheafScalars.functor k X).obj M

def addEquiv (M : X.left.Modules) (n : ℕ) :
    Ext.{u + 1} (DeRhamGlobalId.DeRhamGlobal.coefficientSheaf k X) (sheaf k X M) n ≃+ SheafCohomology.AffineH.Projective.H M n :=
  BaseSheafCohomology.FlatBaseSheafCohomology.equiv.{u, u + 1, u + 1, u} k J (sheaf k X M) n

omit [Module.Flat ℤ k] in
theorem forget_scalar (M : X.left.Modules) (r : k) :
    (SheafCoefficients.FlatBaseSheafCoefficients.forget k J).map (r • 𝟙 (sheaf k X M)) =
      (SheafOfModules.toSheaf X.left.ringCatSheaf).map
        (SheafCohomology.AffineH.Projective.globalSmulHom M (X.hom.appTop ((Scheme.ΓSpecIso (CommRingCat.of k)).inv r))) := by
  apply Sheaf.hom_ext
  ext U x
  change @SMul.smul (X.left.ringCatSheaf.obj.obj U) (M.val.obj U) (M.val.obj U).isModule.toSMul
      (AlgebraicForms.AlgebraicDeRham.sectionBaseMap k X U.unop r) x =
    @SMul.smul (X.left.ringCatSheaf.obj.obj U) (M.val.obj U) (M.val.obj U).isModule.toSMul
      (X.left.presheaf.map U.unop.leTop.op
        (X.hom.appTop ((Scheme.ΓSpecIso (CommRingCat.of k)).inv r))) x
  exact congrArg (fun a : Γ(X.left, U.unop) =>
    @SMul.smul (X.left.ringCatSheaf.obj.obj U) (M.val.obj U) (M.val.obj U).isModule.toSMul a x)
    (Base.ModuleCoefficientPresheaf.BaseModuleCoefficientPresheaf.constants k X U.unop r).symm

def linearEquiv (M : X.left.Modules) (n : ℕ) :
    letI := NumberTheory.PadicHodge.IntegralComparison.Projective.CoherentFiniteness.coefficientModule k X.hom M n
    Ext.{u + 1} (DeRhamGlobalId.DeRhamGlobal.coefficientSheaf k X) (sheaf k X M) n ≃ₗ[k] SheafCohomology.AffineH.Projective.H M n := by
  letI := NumberTheory.PadicHodge.IntegralComparison.Projective.CoherentFiniteness.coefficientModule k X.hom M n
  refine { addEquiv k X M n with map_smul' := ?_ }
  intro r x
  have h := BaseSheafCohomology.FlatBaseSheafCohomology.naturality.{u, u + 1, u + 1, u}
    k J (r • 𝟙 (sheaf k X M)) n x
  rw [forget_scalar] at h
  exact (congrArg (addEquiv k X M n) (Ext.smul_eq_comp_mk₀ x r)).trans h

theorem finite [IsNoetherianRing k] [IsProper X.hom] (M : X.left.Modules) [M.IsQuasicoherent] [M.IsFiniteType]
    (n : ℕ) : Module.Finite k (Ext.{u + 1} (DeRhamGlobalId.DeRhamGlobal.coefficientSheaf k X) (sheaf k X M) n) := by
  let := NumberTheory.PadicHodge.IntegralComparison.Projective.CoherentFiniteness.coefficientModule k X.hom M n
  let : Module.Finite k (SheafCohomology.AffineH.Projective.H M n) := ProperCoherentCoefficient.ProperCoherentFiniteness.coefficient k X.hom M n
  exact Module.Finite.equiv (linearEquiv k X M n).symm

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.FlatBase.ProperCoherentExt.FlatBaseProperCoherentExt
