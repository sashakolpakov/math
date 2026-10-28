import Mathlib

/-! # Cohomology -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Cohomology

noncomputable section

/-!
# IntegralComparison: rational pro-étale cohomology

The coefficient sheaf is the actual sheaf of continuous Q_l-valued
functions on the pro-étale site. Its cohomology is defined by Ext from
the constant rank-one module sheaf. No finite-dimensionality, Frobenius
trace formula, or comparison assertion is included in these definitions.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

universe u

variable (ℓ : ℕ) [Fact ℓ.Prime]

/-- A universe lift of Q_l; the ring equivalence to Q_l is `ULift.ringEquiv`. -/
abbrev Coeff := ULift.{u + 1} ℚ_[ℓ]

/-- Continuous Q_l-valued functions, as a presheaf of Q_l-vector spaces. -/
def rationalCoefficientPresheaf : Scheme.{u}ᵒᵖ ⥤ ModuleCat.{u + 1} (Coeff.{u} ℓ) where
  obj U := ModuleCat.of (Coeff ℓ) C(U.unop, Coeff ℓ)
  map f := ModuleCat.ofHom
    (ContinuousMap.compCLM (Coeff ℓ) (Coeff ℓ) f.unop.base.hom).toLinearMap

lemma rationalCoefficientPresheaf_isSheaf :
    Presheaf.IsSheaf Scheme.fpqcTopology (rationalCoefficientPresheaf.{u} ℓ) := by
  apply (Presheaf.isSheaf_iff_isSheaf_forget Scheme.fpqcTopology
    (rationalCoefficientPresheaf.{u} ℓ)
    (forget (ModuleCat.{u + 1} (Coeff.{u} ℓ)))).mpr
  exact isSheaf_fpqcTopology_continuousMapPresheaf (Coeff.{u} ℓ)

/-- The rational coefficient sheaf on the small pro-étale site. -/
def rationalCoefficientSheaf (X : Scheme.{u}) :
    Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} (Coeff.{u} ℓ)) :=
  ((Scheme.ProEt.forget X ⋙ Over.forget _).sheafPushforwardContinuous _ _
    Scheme.proetaleTopology).obj
      ⟨rationalCoefficientPresheaf ℓ,
        .of_le Scheme.proetaleTopology_le_fpqcTopology
          (rationalCoefficientPresheaf_isSheaf ℓ)⟩

instance rationalSheavesGrothendieck (X : Scheme.{u}) :
    IsGrothendieckAbelian.{u + 1}
      (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} (Coeff.{u} ℓ))) := by
  have : EssentiallySmall.{u + 1} X.ProEt := inferInstance
  exact Sheaf.isGrothendieckAbelian_of_essentiallySmall
    (Scheme.ProEt.topology X) (ModuleCat.{u + 1} (Coeff.{u} ℓ))

/-- The constant free rank-one coefficient sheaf represents global sections. -/
def constantUnitSheaf (X : Scheme.{u}) :
    Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} (Coeff.{u} ℓ)) :=
  (constantSheaf _ _).obj (ModuleCat.of (Coeff.{u} ℓ) (Coeff.{u} ℓ))

/-- Rational pro-étale cohomology of a scheme in degree n. -/
def RationalEllAdicCohomology (X : Scheme.{u}) (n : ℕ) : Type (u + 1) :=
  Abelian.Ext (constantUnitSheaf ℓ X) (rationalCoefficientSheaf ℓ X) n

instance rationalCohomologyAddCommGroup (X : Scheme.{u}) (n : ℕ) :
    AddCommGroup (RationalEllAdicCohomology ℓ X n) := by
  unfold RationalEllAdicCohomology
  infer_instance

instance rationalCohomologyLiftedModule (X : Scheme.{u}) (n : ℕ) :
    Module (Coeff.{u} ℓ) (RationalEllAdicCohomology ℓ X n) := by
  unfold RationalEllAdicCohomology
  infer_instance

instance rationalCohomologyModule (X : Scheme.{u}) (n : ℕ) :
    Module ℚ_[ℓ] (RationalEllAdicCohomology ℓ X n) :=
  Module.compHom _ (ULift.ringEquiv : Coeff.{u} ℓ ≃+* ℚ_[ℓ]).symm.toRingHom

instance rationalCohomologyScalarTower (X : Scheme.{u}) (n : ℕ) :
    IsScalarTower ℚ_[ℓ] (Coeff.{u} ℓ) (RationalEllAdicCohomology ℓ X n) where
  smul_assoc a b x := by
    change ((ULift.up a : Coeff.{u} ℓ) * b) • x =
      (ULift.up a : Coeff.{u} ℓ) • (b • x)
    exact mul_smul _ _ _

instance rationalCohomologyCompatibleSMul (X Y : Scheme.{u}) (n m : ℕ) :
    LinearMap.CompatibleSMul (RationalEllAdicCohomology ℓ X n)
      (RationalEllAdicCohomology ℓ Y m) ℚ_[ℓ] (Coeff.{u} ℓ) where
  map_smul g c x := by
    change g ((ULift.up c : Coeff.{u} ℓ) • x) = (ULift.up c : Coeff.{u} ℓ) • g x
    exact g.map_smul _ _

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Cohomology
