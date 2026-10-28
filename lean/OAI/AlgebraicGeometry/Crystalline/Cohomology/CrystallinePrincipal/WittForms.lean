import OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallinePrincipal.CechAugmentation
import OAI.AlgebraicGeometry.Crystalline.Cohomology.ScalarRestriction

/-! # Witt Forms -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallinePrincipal.WittForms.CrystallinePrincipalWittForms

noncomputable section

/-!
# Witt-scalar identification with the native frame-resolution functor

Restricting the ambient-ring linear diagram to Witt scalars recovers the
actual degree of the native Koszul frame resolution on principal opens.
The comparison is the identity on the underlying form tensors.
-/

open _root_.CategoryTheory Limits Opposite
open scoped TensorProduct

universe u

variable (p : ℕ) [Fact p.Prime] (k B σ : Type u) [Field k] [CharP k p]
  [CommRing B] [Algebra k B] [Fintype σ] (a : σ → B)
  (Q : Site.Object p k (AffineFrameCover.CrystallineAffineFrameCover.affineScheme k B)) (n : ℕ)

local notation "QR" => Q.thickening.ring
local notation "W" => WittVector p k
local notation "X" => OAI.AlgebraicGeometry.Crystalline.Cohomology.AffineFrameCover.CrystallineAffineFrameCover.affineScheme k B

def scalars : ModuleCat.{u} QR ⥤ ModuleCat.{u} W :=
  ModuleCat.restrictScalars (algebraMap W QR)

def nativeFunctor : (PrincipalCoefficient.PrincipalCoefficientCategory.Object QR)ᵒᵖ ⥤ ModuleCat.{u} W :=
  (Functor.CrystallinePrincipalFunctor.functor p k X Q).op ⋙
    Koszul.Functor.KoszulFunctor.functor W σ (CrystallineFrame.Operators.CrystallineFrameOperators.functions p k B σ a)
      (CrystallineFrame.Operators.CrystallineFrameOperators.derivative p k B σ a) (CrystallineFrame.Resolution.CrystallineFrameResolution.commute p k B σ a) ⋙
    HomologicalComplex.eval (ModuleCat.{u} W) (ComplexShape.up ℕ) n

def objectIso (r : (PrincipalCoefficient.PrincipalCoefficientCategory.Object QR)ᵒᵖ) :
    (nativeFunctor p k B σ a Q n).obj r ≅
      ((FormsFunctor.CrystallinePrincipalFormsFunctor.functor p k B σ a Q n) ⋙ scalars p k B Q).obj r := by
  letI : Module W (FormsFunctor.CrystallinePrincipalFormsFunctor.object p k B σ Q n r) :=
    ((nativeFunctor p k B σ a Q n).obj r).isModule
  letI : IsScalarTower W QR (FormsFunctor.CrystallinePrincipalFormsFunctor.object p k B σ Q n r) :=
    inferInstanceAs (IsScalarTower W QR
      (Koszul.Tensor.KoszulTensor.Term W σ (FrameMaps.CrystallinePrincipalFrameMaps.Ring p k B σ Q r.unop) n))
  exact ScalarRestriction.ScalarRestrictionIso.iso W QR (FormsFunctor.CrystallinePrincipalFormsFunctor.object p k B σ Q n r)

def functorIso : nativeFunctor p k B σ a Q n ≅
    FormsFunctor.CrystallinePrincipalFormsFunctor.functor p k B σ a Q n ⋙ scalars p k B Q :=
  NatIso.ofComponents (objectIso p k B σ a Q n) (by
    intro r s f
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    have hn := LinearMap.congr_fun (FrameMaps.CrystallinePrincipalFrameMaps.native_map p k B σ a Q f.unop n) x
    have hm := congrArg (fun h : FormsFunctor.CrystallinePrincipalFormsFunctor.object p k B σ Q n r ⟶
        FormsFunctor.CrystallinePrincipalFormsFunctor.object p k B σ Q n s => h.hom x)
      (FormsFunctor.CrystallinePrincipalFormsFunctor.map_eq_native p k B σ a Q n f.unop)
    exact hn.trans hm.symm)

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallinePrincipal.WittForms.CrystallinePrincipalWittForms
