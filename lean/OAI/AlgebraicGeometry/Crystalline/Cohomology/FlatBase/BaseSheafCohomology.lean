import OAI.AlgebraicGeometry.Crystalline.Cohomology.FlatBase.SheafCoefficients
import OAI.NumberTheory.PadicHodge.IntegralComparison.CoefficientConstants
import OAI.AlgebraicGeometry.SheafCohomology.ExtNaturality

/-! # Base Sheaf Cohomology -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.FlatBase.BaseSheafCohomology.FlatBaseSheafCohomology

noncomputable section

/-! # Original flat-base coefficient Ext and additive sheaf cohomology -/

open _root_.CategoryTheory _root_.CategoryTheory.Abelian

universe u z₁ z₂ z₃

variable (k : Type u) [CommRing k] [Module.Flat ℤ k]
  {C : Type u} [Category.{u} C] (J : GrothendieckTopology C)

abbrev IntegerRing : Type u := SheafCoefficients.FlatBaseSheafCoefficients.Integers

attribute [local instance] SheafCoefficients.FlatBaseSheafCoefficients.integerAlgebra

variable [HasSheafify J (ModuleCat.{u} IntegerRing)] [HasSheafify J (ModuleCat.{u} k)]
  [HasSheafify J AddCommGrpCat.{u}]
  [HasExt.{z₁} (Sheaf J (ModuleCat.{u} k))]
  [HasExt.{z₂} (Sheaf J (ModuleCat.{u} IntegerRing))]
  [HasExt.{z₃} (Sheaf J AddCommGrpCat.{u})]
  [EnoughInjectives (Sheaf J (ModuleCat.{u} k))]
  [EnoughInjectives (Sheaf J (ModuleCat.{u} IntegerRing))]

abbrev fieldConstant := (constantSheaf J (ModuleCat.{u} k)).obj (ModuleCat.of k k)

abbrev integerConstant := (constantSheaf J (ModuleCat.{u} IntegerRing)).obj (ModuleCat.of IntegerRing IntegerRing)

abbrev additiveConstant := (constantSheaf J AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift.{u} ℤ))

def integerEquiv (M N : Sheaf J (ModuleCat.{u} IntegerRing)) (n : ℕ) :
    Ext.{z₂} M N n ≃+ Ext.{z₃} ((SmallInteger.SmallIntegerSheafCoefficients.forget J).obj M)
      ((SmallInteger.SmallIntegerSheafCoefficients.forget J).obj N) n :=
  AddEquiv.ofBijective ((SmallInteger.SmallIntegerSheafCoefficients.forget J).mapExtAddHom M N n)
    ((SmallInteger.SmallIntegerSheafCoefficients.forget J).mapExt_bijective_of_preservesInjectiveObjects M N n)

def equiv (N : Sheaf J (ModuleCat.{u} k)) (n : ℕ) :
    Ext.{z₁} (fieldConstant k J) N n ≃+
      Ext.{z₃} (additiveConstant J) ((SheafCoefficients.FlatBaseSheafCoefficients.forget k J).obj N) n :=
  (SheafCohomology.ExtLeft.Projective.extLeftIso (NumberTheory.PadicHodge.IntegralComparison.CoefficientConstants.extensionConstantIso IntegerRing k J).symm N n).trans
    ((SheafCohomology.ExtAdjunction.Projective.extAdjunction (SheafCoefficients.FlatBaseSheafCoefficients.restriction k J)
      (integerConstant J) (NumberTheory.PadicHodge.IntegralComparison.FlatCoefficientSheaves.adjunction IntegerRing k J) N n).trans
        ((integerEquiv J (integerConstant J)
          ((SheafCoefficients.FlatBaseSheafCoefficients.restriction k J).obj N) n).trans
            (SheafCohomology.ExtLeft.Projective.extLeftIso (SmallInteger.SmallIntegerSheafCoefficients.constantIso J)
              ((SheafCoefficients.FlatBaseSheafCoefficients.forget k J).obj N) n)))

theorem naturality {M N : Sheaf J (ModuleCat.{u} k)} (f : M ⟶ N) (n : ℕ)
    (x : Ext.{z₁} (fieldConstant k J) M n) :
    equiv k J N n (x.comp (Ext.mk₀ f) (Nat.add_zero n)) =
      (equiv k J M n x).comp (Ext.mk₀ ((SheafCoefficients.FlatBaseSheafCoefficients.forget k J).map f))
        (Nat.add_zero n) := by
  let I := integerConstant J
  let F := SheafCoefficients.FlatBaseSheafCoefficients.restriction k J
  let G := SmallInteger.SmallIntegerSheafCoefficients.forget J
  let e := NumberTheory.PadicHodge.IntegralComparison.CoefficientConstants.extensionConstantIso IntegerRing k J
  let a (T : Sheaf J (ModuleCat.{u} k)) := SheafCohomology.ExtLeft.Projective.extLeftIso e.symm T n
  let b (T : Sheaf J (ModuleCat.{u} k)) := SheafCohomology.ExtAdjunction.Projective.extAdjunction F I
    (NumberTheory.PadicHodge.IntegralComparison.FlatCoefficientSheaves.adjunction IntegerRing k J) T n
  let c (T : Sheaf J (ModuleCat.{u} k)) := integerEquiv J I (F.obj T) n
  let d (T : Sheaf J (ModuleCat.{u} k)) := SheafCohomology.ExtLeft.Projective.extLeftIso
    (SmallInteger.SmallIntegerSheafCoefficients.constantIso J) (G.obj (F.obj T)) n
  have h₁ := SheafCohomology.ExtNaturality.Projective.extLeftIso_naturality e.symm f n x
  have h₂ := SheafCohomology.ExtNaturality.Projective.extCompare_naturality F I ((NumberTheory.PadicHodge.IntegralComparison.FlatCoefficientSheaves.extension IntegerRing k J).obj I)
    ((NumberTheory.PadicHodge.IntegralComparison.FlatCoefficientSheaves.adjunction IntegerRing k J).unit.app I) f n (a M x)
  have h₃ : c N ((b M (a M x)).comp (Ext.mk₀ (F.map f)) (Nat.add_zero n)) =
      (c M (b M (a M x))).comp (Ext.mk₀ (G.map (F.map f))) (Nat.add_zero n) := by
    change ((b M (a M x)).comp (Ext.mk₀ (F.map f)) (Nat.add_zero n)).mapExactFunctor G = _
    rw [Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀]
    rfl
  have h₄ := SheafCohomology.ExtNaturality.Projective.extLeftIso_naturality (SmallInteger.SmallIntegerSheafCoefficients.constantIso J)
    (G.map (F.map f)) n (c M (b M (a M x)))
  change d N (c N (b N (a N (x.comp (Ext.mk₀ f) (Nat.add_zero n))))) = _
  exact (congrArg (fun z => d N (c N (b N z))) h₁).trans
    ((congrArg (fun z => d N (c N z)) h₂).trans ((congrArg (d N) h₃).trans h₄))

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.FlatBase.BaseSheafCohomology.FlatBaseSheafCohomology
