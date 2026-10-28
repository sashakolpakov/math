import OAI.NumberTheory.PadicHodge.GeometricComparison.Integral.ConstantCoefficientExtension
import OAI.AlgebraicGeometry.SheafCohomology.ExtNaturality

/-! # Additive Sheaf Cohomology -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Integral.AdditiveSheafCohomology.IntegralAdditiveSheafCohomology

noncomputable section

/-! Comparison of the actual integral coefficient Ext definition with additive sheaf cohomology, including coefficient-map naturality. -/

open _root_.CategoryTheory _root_.CategoryTheory.Abelian

open OAI.NumberTheory.PadicHodge.GeometricComparison.Integral.SheafCoefficientAdjunction.IntegralSheafCoefficientAdjunction OAI.NumberTheory.PadicHodge.GeometricComparison.Integral.IntegerSheafEquivalence.IntegralIntegerSheafEquivalence OAI.NumberTheory.PadicHodge.GeometricComparison.Integral.ConstantCoefficientExtension.IntegralConstantCoefficientExtension

variable (R : Type) [CommRing R] [Module.Flat ℤ R]
  {C : Type} [Category.{0} C] (J : GrothendieckTopology C)
  [HasExt.{1} (Sheaf J (ModuleCat.{0} R))]
  [HasExt.{0} (Sheaf J (ModuleCat.{0} ℤ))]
  [HasExt.{0} (Sheaf J AddCommGrpCat.{0})]

abbrev integerConstant := (constantSheaf J (ModuleCat.{0} ℤ)).obj (ModuleCat.of ℤ (ULift.{0} ℤ))

abbrev fieldConstant := (constantSheaf J (ModuleCat.{0} R)).obj (ModuleCat.of R R)

abbrev additiveConstant := (constantSheaf J AddCommGrpCat.{0}).obj (AddCommGrpCat.of (ULift.{0} ℤ))

abbrev underlyingSheaf (N : Sheaf J (ModuleCat.{0} R)) :=
  (IntegerSheafEquivalence.IntegralIntegerSheafEquivalence.forgetSheaf J).obj ((SheafCoefficientAdjunction.IntegralSheafCoefficientAdjunction.restrictSheaf R J).obj N)

def equiv (N : Sheaf J (ModuleCat.{0} R)) (n : ℕ) :
    Ext (fieldConstant R J) N n ≃+ Ext (additiveConstant J) (underlyingSheaf R J N) n :=
  (AlgebraicGeometry.SheafCohomology.ExtLeft.Projective.extLeftIso (ConstantCoefficientExtension.IntegralConstantCoefficientExtension.constantIso R J).symm N n).trans
    ((SheafCoefficientAdjunction.IntegralSheafCoefficientAdjunction.extAdjunction R J (integerConstant J) N n).trans
      ((IntegerSheafEquivalence.IntegralIntegerSheafEquivalence.extEquiv J (integerConstant J) ((SheafCoefficientAdjunction.IntegralSheafCoefficientAdjunction.restrictSheaf R J).obj N) n).trans
        (AlgebraicGeometry.SheafCohomology.ExtLeft.Projective.extLeftIso (ConstantCoefficientExtension.IntegralConstantCoefficientExtension.forgetConstantIso J) (underlyingSheaf R J N) n)))

theorem naturality {M N : Sheaf J (ModuleCat.{0} R)} (f : M ⟶ N) (n : ℕ)
    (x : Ext (fieldConstant R J) M n) :
    equiv R J N n (x.comp (Ext.mk₀ f) (Nat.add_zero n)) =
      (equiv R J M n x).comp
        (Ext.mk₀ ((IntegerSheafEquivalence.IntegralIntegerSheafEquivalence.forgetSheaf J).map ((SheafCoefficientAdjunction.IntegralSheafCoefficientAdjunction.restrictSheaf R J).map f))) (Nat.add_zero n) := by
  let I := integerConstant J
  let F := SheafCoefficientAdjunction.IntegralSheafCoefficientAdjunction.restrictSheaf R J
  let G := IntegerSheafEquivalence.IntegralIntegerSheafEquivalence.forgetSheaf J
  let a (T : Sheaf J (ModuleCat.{0} R)) := AlgebraicGeometry.SheafCohomology.ExtLeft.Projective.extLeftIso (ConstantCoefficientExtension.IntegralConstantCoefficientExtension.constantIso R J).symm T n
  let b (T : Sheaf J (ModuleCat.{0} R)) := SheafCoefficientAdjunction.IntegralSheafCoefficientAdjunction.extAdjunction R J I T n
  let c (T : Sheaf J (ModuleCat.{0} R)) := IntegerSheafEquivalence.IntegralIntegerSheafEquivalence.extEquiv J I (F.obj T) n
  let d (T : Sheaf J (ModuleCat.{0} R)) :=
    AlgebraicGeometry.SheafCohomology.ExtLeft.Projective.extLeftIso (ConstantCoefficientExtension.IntegralConstantCoefficientExtension.forgetConstantIso J) (G.obj (F.obj T)) n
  have h₁ := AlgebraicGeometry.SheafCohomology.ExtNaturality.Projective.extLeftIso_naturality (ConstantCoefficientExtension.IntegralConstantCoefficientExtension.constantIso R J).symm f n x
  have h₂ := AlgebraicGeometry.SheafCohomology.ExtNaturality.Projective.extCompare_naturality F I ((SheafCoefficientAdjunction.IntegralSheafCoefficientAdjunction.extendSheaf R J).obj I)
    ((SheafCoefficientAdjunction.IntegralSheafCoefficientAdjunction.adjunction R J).unit.app I) f n (a M x)
  have h₃ : c N ((b M (a M x)).comp (Ext.mk₀ (F.map f)) (Nat.add_zero n)) =
      (c M (b M (a M x))).comp (Ext.mk₀ (G.map (F.map f))) (Nat.add_zero n) := by
    change ((b M (a M x)).comp (Ext.mk₀ (F.map f)) (Nat.add_zero n)).mapExactFunctor G = _
    rw [Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀]
    rfl
  have h₄ := AlgebraicGeometry.SheafCohomology.ExtNaturality.Projective.extLeftIso_naturality (ConstantCoefficientExtension.IntegralConstantCoefficientExtension.forgetConstantIso J) (G.map (F.map f)) n
    (c M (b M (a M x)))
  change d N (c N (b N (a N (x.comp (Ext.mk₀ f) (Nat.add_zero n))))) = _
  exact (congrArg (fun z => d N (c N (b N z))) h₁).trans
    ((congrArg (fun z => d N (c N z)) h₂).trans ((congrArg (d N) h₃).trans h₄))

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Integral.AdditiveSheafCohomology.IntegralAdditiveSheafCohomology
