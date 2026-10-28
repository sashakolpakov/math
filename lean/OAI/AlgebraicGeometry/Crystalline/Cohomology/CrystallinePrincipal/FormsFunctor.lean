import OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallinePrincipal.FrameNaturality

/-! # Forms Functor -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallinePrincipal.FormsFunctor.CrystallinePrincipalFormsFunctor

noncomputable section

/-!
# The functor of native principal frame forms

Transport the associated module sheaf along the proved section
equivalences. Its arrows are then identified with the actual native
frame maps, so the resulting natural isomorphism compares whole diagrams.
-/

open _root_.CategoryTheory Limits Opposite
open scoped TensorProduct

universe u

variable (p : ℕ) [Fact p.Prime] (k B σ : Type u) [Field k] [CharP k p]
  [CommRing B] [Algebra k B] (a : σ → B)
  (Q : Site.Object p k (AffineFrameCover.CrystallineAffineFrameCover.affineScheme k B)) (n : ℕ)

local notation "QR" => Q.thickening.ring
local notation "W" => WittVector p k

def object (r : (PrincipalCoefficient.PrincipalCoefficientCategory.Object QR)ᵒᵖ) : ModuleCat.{u} QR := by
  let S := Localization.Away r.unop.val
  letI : CommRing S := inferInstance
  letI : Algebra W S := inferInstance
  let G := DividedPowerAlgebra S (σ →₀ S)
  let T := Functor.CrystallinePrincipalFunctor.object p k (AffineFrameCover.CrystallineAffineFrameCover.affineScheme k B) Q r.unop
  letI : CommRing G := inferInstanceAs
    (CommRing (PolynomialThickening.CrystallinePolynomialThickening.thickening p k T.residueRing σ T.thickening).ring)
  letI : Module W G := inferInstance
  letI : AddCommGroup (Koszul.Tensor.KoszulTensor.Term W σ G n) := inferInstanceAs
    (AddCommGroup (CrystallineFrame.PrincipalForms.CrystallineFramePrincipalForms.module p k B σ T n))
  exact ModuleCat.of QR (Koszul.Tensor.KoszulTensor.Term W σ G n)

def componentIso (r : (PrincipalCoefficient.PrincipalCoefficientCategory.Object QR)ᵒᵖ) :
    object p k B σ Q n r ≅ (FrameNaturality.CrystallinePrincipalFrameNaturality.coefficients p k B σ Q n).obj r :=
  (CrystallineFrame.PrincipalForms.CrystallineFramePrincipalForms.sectionsEquiv p k B σ a Q n r.unop.val).toModuleIso

def functor : (PrincipalCoefficient.PrincipalCoefficientCategory.Object QR)ᵒᵖ ⥤ ModuleCat.{u} QR where
  obj := object p k B σ Q n
  map {r s} f := (componentIso p k B σ a Q n r).hom ≫
    (FrameNaturality.CrystallinePrincipalFrameNaturality.coefficients p k B σ Q n).map f ≫
      (componentIso p k B σ a Q n s).inv
  map_id r := by simp
  map_comp f g := by simp

def sectionsIso : functor p k B σ a Q n ≅ FrameNaturality.CrystallinePrincipalFrameNaturality.coefficients p k B σ Q n :=
  NatIso.ofComponents (componentIso p k B σ a Q n) (by
    intro r s f
    change ((componentIso p k B σ a Q n r).hom ≫
      (FrameNaturality.CrystallinePrincipalFrameNaturality.coefficients p k B σ Q n).map f ≫
        (componentIso p k B σ a Q n s).inv) ≫ (componentIso p k B σ a Q n s).hom = _
    simp
    rfl)

theorem map_eq_native {r s : PrincipalCoefficient.PrincipalCoefficientCategory.Object Q.thickening.ring} (f : r ⟶ s) :
    (functor p k B σ a Q n).map f.op =
      ModuleCat.ofHom (X := object p k B σ Q n (op s)) (Y := object p k B σ Q n (op r))
        (FrameMaps.CrystallinePrincipalFrameMaps.moduleMap p k B σ a Q f n) := by
  have he : ModuleCat.ofHom (X := object p k B σ Q n (op s)) (Y := object p k B σ Q n (op r))
      (FrameMaps.CrystallinePrincipalFrameMaps.moduleMap p k B σ a Q f n) ≫
      (componentIso p k B σ a Q n (op r)).hom =
    (componentIso p k B σ a Q n (op s)).hom ≫
      (FrameNaturality.CrystallinePrincipalFrameNaturality.coefficients p k B σ Q n).map f.op := by
    apply ModuleCat.hom_ext
    exact FrameNaturality.CrystallinePrincipalFrameNaturality.sections_naturality p k B σ a Q n f
  apply (cancel_mono (componentIso p k B σ a Q n (op r)).hom).mp
  exact (sectionsIso p k B σ a Q n).hom.naturality f.op |>.trans he.symm

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallinePrincipal.FormsFunctor.CrystallinePrincipalFormsFunctor
