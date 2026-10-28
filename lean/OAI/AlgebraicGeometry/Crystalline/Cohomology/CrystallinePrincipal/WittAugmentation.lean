import OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallinePrincipal.WittCech

/-! # Witt Augmentation -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallinePrincipal.WittAugmentation.CrystallinePrincipalWittAugmentation

noncomputable section

/-!
# The augmented Čech computation in native Witt coefficients

This quasi-isomorphism starts with an actual term of the native frame
resolution on the original crystalline object and ends in its native
principal-open Čech complex. All scalar restrictions are explicit.
-/

open _root_.CategoryTheory Limits Opposite
open scoped TensorProduct

universe u

variable (p : ℕ) [Fact p.Prime] (k B σ : Type u) [Field k] [CharP k p]
  [CommRing B] [Algebra k B] [Fintype σ] (a : σ → B)
  (Q : Site.Object p k (AffineFrameCover.CrystallineAffineFrameCover.affineScheme k B)) (n : ℕ)

local notation "QR" => Q.thickening.ring
local notation "W" => WittVector p k

local instance scalars_additive : (WittForms.CrystallinePrincipalWittForms.scalars p k B Q).Additive := by
  dsimp [WittForms.CrystallinePrincipalWittForms.scalars]
  infer_instance

local instance scalars_homology : (WittForms.CrystallinePrincipalWittForms.scalars p k B Q).PreservesHomology :=
  ScalarRestriction.ScalarRestrictionIso.restrictScalars_preservesHomology (algebraMap W QR)

def source : ModuleCat.{u} W :=
  (Koszul.Functor.KoszulFunctor.object W σ (CrystallineFrame.Operators.CrystallineFrameOperators.functions p k B σ a)
    (CrystallineFrame.Operators.CrystallineFrameOperators.derivative p k B σ a) (CrystallineFrame.Resolution.CrystallineFrameResolution.commute p k B σ a) (op Q)).X n

def sourceIso : source p k B σ a Q n ≅
    (WittForms.CrystallinePrincipalWittForms.scalars p k B Q).obj (CrystallineFrame.PrincipalForms.CrystallineFramePrincipalForms.module p k B σ Q n) := by
  letI : Module W (CrystallineFrame.PrincipalForms.CrystallineFramePrincipalForms.module p k B σ Q n) := (source p k B σ a Q n).isModule
  letI : IsScalarTower W QR (CrystallineFrame.PrincipalForms.CrystallineFramePrincipalForms.module p k B σ Q n) :=
    inferInstanceAs (IsScalarTower W QR (Koszul.Tensor.KoszulTensor.Term W σ (DividedPowerAlgebra QR (σ →₀ QR)) n))
  exact ScalarRestriction.ScalarRestrictionIso.iso W QR (CrystallineFrame.PrincipalForms.CrystallineFramePrincipalForms.module p k B σ Q n)

def sourceComplexIso : (CochainComplex.single₀ (ModuleCat.{u} W)).obj (source p k B σ a Q n) ≅
    ((WittForms.CrystallinePrincipalWittForms.scalars p k B Q).mapHomologicalComplex (ComplexShape.up ℕ)).obj
      ((CochainComplex.single₀ (ModuleCat.{u} QR)).obj (CrystallineFrame.PrincipalForms.CrystallineFramePrincipalForms.module p k B σ Q n)) :=
  (CochainComplex.single₀ (ModuleCat.{u} W)).mapIso (sourceIso p k B σ a Q n) ≪≫
    ((HomologicalComplex.singleMapHomologicalComplex (WittForms.CrystallinePrincipalWittForms.scalars p k B Q)
      (ComplexShape.up ℕ) 0).app (CrystallineFrame.PrincipalForms.CrystallineFramePrincipalForms.module p k B σ Q n)).symm

variable {ι : Type u} [Finite ι] (s : ι → Q.thickening.ring)

def augmentation : (CochainComplex.single₀ (ModuleCat.{u} W)).obj (source p k B σ a Q n) ⟶
    WittCech.CrystallinePrincipalWittCech.complex p k B σ a Q n s :=
  (sourceComplexIso p k B σ a Q n).hom ≫
    ((WittForms.CrystallinePrincipalWittForms.scalars p k B Q).mapHomologicalComplex (ComplexShape.up ℕ)).map
      (CechAugmentation.CrystallinePrincipalCechAugmentation.augmentation p k B σ a Q n s) ≫
    (WittCech.CrystallinePrincipalWittCech.complexIso p k B σ a Q n s).inv

theorem quasiIso (hs : Ideal.span (Set.range s) = ⊤) : QuasiIso (augmentation p k B σ a Q n s) := by
  have hq : QuasiIso (CechAugmentation.CrystallinePrincipalCechAugmentation.augmentation p k B σ a Q n s) :=
    CechAugmentation.CrystallinePrincipalCechAugmentation.quasiIso p k B σ a Q n s hs
  have hm : QuasiIso (((WittForms.CrystallinePrincipalWittForms.scalars p k B Q).mapHomologicalComplex
      (ComplexShape.up ℕ)).map (CechAugmentation.CrystallinePrincipalCechAugmentation.augmentation p k B σ a Q n s)) :=
    inferInstance
  have hsrc : QuasiIso (sourceComplexIso p k B σ a Q n).hom :=
    HomotopyEquiv.quasiIso_hom (HomotopyEquiv.ofIso (sourceComplexIso p k B σ a Q n))
  have htgt : QuasiIso (WittCech.CrystallinePrincipalWittCech.complexIso p k B σ a Q n s).inv :=
    HomotopyEquiv.quasiIso_hom (HomotopyEquiv.ofIso (WittCech.CrystallinePrincipalWittCech.complexIso p k B σ a Q n s).symm)
  have hi := quasiIso_comp _ _ (hφ := hm) (hφ' := htgt)
  exact quasiIso_comp _ _ (hφ := hsrc) (hφ' := hi)

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallinePrincipal.WittAugmentation.CrystallinePrincipalWittAugmentation
