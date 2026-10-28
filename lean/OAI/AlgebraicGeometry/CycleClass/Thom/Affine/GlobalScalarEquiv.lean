import OAI.AlgebraicGeometry.CycleClass.Thom.SmoothAffineGlobalCoordinates
import OAI.AlgebraicGeometry.CycleClass.Thom.EtaleCoordinateTransport

/-! # Global Scalar Equiv -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Affine.GlobalScalarEquiv.Constructions

noncomputable section

/-! The canonical global-section algebra on an affine spectrum is
the original coefficient algebra. This identifies actual global
etale coordinates with coordinates on their presented affine ring. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (A : Type) [CommRing A] [Algebra ℂ A]

local instance : IsAffine (Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ A).left := inferInstanceAs (IsAffine (Spec (CommRingCat.of A)))

local instance : Algebra ℂ Γ((Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ A).left, ⊤) := Foundations.Scheme.AffineSchemeComplexPoints.affineOverGammaAlgebra (Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ A)

def specGammaAlgEquiv : Γ((Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ A).left, ⊤) ≃ₐ[ℂ] A := by
  refine { (Scheme.ΓSpecIso (CommRingCat.of A)).commRingCatIsoToRingEquiv with commutes' := ?_ }
  intro r
  have h : CommRingCat.ofHom (algebraMap ℂ Γ((Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ A).left, ⊤)) ≫
      (Scheme.ΓSpecIso (CommRingCat.of A)).hom = CommRingCat.ofHom (algebraMap ℂ A) := by
    apply Spec.map_injective
    rw [Spec.map_comp, ← Scheme.isoSpec_Spec_hom]
    change (Spec (CommRingCat.of A)).isoSpec.hom ≫
      Spec.map (Spec.preimage ((Spec (CommRingCat.of A)).isoSpec.inv ≫
        Spec.map (CommRingCat.ofHom (algebraMap ℂ A)))) = _
    rw [Spec.map_preimage, Iso.hom_inv_id_assoc]
  exact ConcreteCategory.congr_hom h r

theorem exists_global_etale_coordinates (n : ℕ) [Algebra (MvPolynomial (Fin n) ℂ) A]
    [IsScalarTower ℂ (MvPolynomial (Fin n) ℂ) A]
    [Algebra.IsStandardEtale (MvPolynomial (Fin n) ℂ) A] :
    ∃ a : Algebra (MvPolynomial (Fin n) ℂ) Γ((Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ A).left, ⊤), letI := a
      IsScalarTower ℂ (MvPolynomial (Fin n) ℂ) Γ((Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ A).left, ⊤) ∧
        Algebra.IsStandardEtale (MvPolynomial (Fin n) ℂ) Γ((Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ A).left, ⊤) :=
  EtaleCoordinateTransport.Constructions.exists_standardEtale_coordinates (P := MvPolynomial (Fin n) ℂ) (specGammaAlgEquiv A).symm

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Affine.GlobalScalarEquiv.Constructions
