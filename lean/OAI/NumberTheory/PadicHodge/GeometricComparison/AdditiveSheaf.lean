import OAI.NumberTheory.PadicHodge.GeometricComparison.ConstantCoefficientUnit
import OAI.AlgebraicGeometry.SheafCohomology.ExtNaturality

/-! # Additive Sheaf -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.AdditiveSheaf.AdditiveSheafCohomology

noncomputable section

/-! Comparison of the actual field-linear Ext definition with additive sheaf cohomology, including coefficient-map naturality. -/

open _root_.CategoryTheory _root_.CategoryTheory.Abelian

open OAI.NumberTheory.PadicHodge.GeometricComparison.SheafCoefficientCo.SheafCoefficientAdjunction OAI.NumberTheory.PadicHodge.GeometricComparison.IntegerSheaf.IntegerSheafEquivalence OAI.NumberTheory.PadicHodge.GeometricComparison.ConstantCoefficientUnit.ConstantCoefficientExtension

variable (R : Type 1) [Field R] [CharZero R]
  {C : Type 1} [Category.{0} C] (J : GrothendieckTopology C)
  [HasExt.{1} (Sheaf J (ModuleCat.{1} R))]
  [HasExt.{1} (Sheaf J (ModuleCat.{1} ℤ))]
  [HasExt.{1} (Sheaf J AddCommGrpCat.{1})]

abbrev integerConstant := (constantSheaf J (ModuleCat.{1} ℤ)).obj (ModuleCat.of ℤ (ULift.{1} ℤ))

abbrev fieldConstant := (constantSheaf J (ModuleCat.{1} R)).obj (ModuleCat.of R R)

abbrev additiveConstant := (constantSheaf J AddCommGrpCat.{1}).obj (AddCommGrpCat.of (ULift.{1} ℤ))

abbrev underlyingSheaf (N : Sheaf J (ModuleCat.{1} R)) :=
  (IntegerSheaf.IntegerSheafEquivalence.forgetSheaf J).obj ((SheafCoefficientCo.SheafCoefficientAdjunction.restrictSheaf R J).obj N)

def equiv (N : Sheaf J (ModuleCat.{1} R)) (n : ℕ) :
    Ext (fieldConstant R J) N n ≃+ Ext (additiveConstant J) (underlyingSheaf R J N) n :=
  (AlgebraicGeometry.SheafCohomology.ExtLeft.Projective.extLeftIso (ConstantCoefficientUnit.ConstantCoefficientExtension.constantIso R J).symm N n).trans
    ((SheafCoefficientCo.SheafCoefficientAdjunction.extAdjunction R J (integerConstant J) N n).trans
      ((IntegerSheaf.IntegerSheafEquivalence.extEquiv J (integerConstant J) ((SheafCoefficientCo.SheafCoefficientAdjunction.restrictSheaf R J).obj N) n).trans
        (AlgebraicGeometry.SheafCohomology.ExtLeft.Projective.extLeftIso (ConstantCoefficientUnit.ConstantCoefficientExtension.forgetConstantIso J) (underlyingSheaf R J N) n)))

theorem naturality {M N : Sheaf J (ModuleCat.{1} R)} (f : M ⟶ N) (n : ℕ)
    (x : Ext (fieldConstant R J) M n) :
    equiv R J N n (x.comp (Ext.mk₀ f) (Nat.add_zero n)) =
      (equiv R J M n x).comp
        (Ext.mk₀ ((IntegerSheaf.IntegerSheafEquivalence.forgetSheaf J).map ((SheafCoefficientCo.SheafCoefficientAdjunction.restrictSheaf R J).map f))) (Nat.add_zero n) := by
  let I := integerConstant J
  let F := SheafCoefficientCo.SheafCoefficientAdjunction.restrictSheaf R J
  let G := IntegerSheaf.IntegerSheafEquivalence.forgetSheaf J
  let a (T : Sheaf J (ModuleCat.{1} R)) := AlgebraicGeometry.SheafCohomology.ExtLeft.Projective.extLeftIso (ConstantCoefficientUnit.ConstantCoefficientExtension.constantIso R J).symm T n
  let b (T : Sheaf J (ModuleCat.{1} R)) := SheafCoefficientCo.SheafCoefficientAdjunction.extAdjunction R J I T n
  let c (T : Sheaf J (ModuleCat.{1} R)) := IntegerSheaf.IntegerSheafEquivalence.extEquiv J I (F.obj T) n
  let d (T : Sheaf J (ModuleCat.{1} R)) :=
    AlgebraicGeometry.SheafCohomology.ExtLeft.Projective.extLeftIso (ConstantCoefficientUnit.ConstantCoefficientExtension.forgetConstantIso J) (G.obj (F.obj T)) n
  have h₁ := AlgebraicGeometry.SheafCohomology.ExtNaturality.Projective.extLeftIso_naturality (ConstantCoefficientUnit.ConstantCoefficientExtension.constantIso R J).symm f n x
  have h₂ := AlgebraicGeometry.SheafCohomology.ExtNaturality.Projective.extCompare_naturality F I ((SheafCoefficientCo.SheafCoefficientAdjunction.extendSheaf R J).obj I)
    ((SheafCoefficientCo.SheafCoefficientAdjunction.adjunction R J).unit.app I) f n (a M x)
  have h₃ : c N ((b M (a M x)).comp (Ext.mk₀ (F.map f)) (Nat.add_zero n)) =
      (c M (b M (a M x))).comp (Ext.mk₀ (G.map (F.map f))) (Nat.add_zero n) := by
    change ((b M (a M x)).comp (Ext.mk₀ (F.map f)) (Nat.add_zero n)).mapExactFunctor G = _
    rw [Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀]
    rfl
  have h₄ := AlgebraicGeometry.SheafCohomology.ExtNaturality.Projective.extLeftIso_naturality (ConstantCoefficientUnit.ConstantCoefficientExtension.forgetConstantIso J) (G.map (F.map f)) n
    (c M (b M (a M x)))
  change d N (c N (b N (a N (x.comp (Ext.mk₀ f) (Nat.add_zero n))))) = _
  exact (congrArg (fun z => d N (c N (b N z))) h₁).trans
    ((congrArg (fun z => d N (c N z)) h₂).trans ((congrArg (d N) h₃).trans h₄))

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.AdditiveSheaf.AdditiveSheafCohomology
