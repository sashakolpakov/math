import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OrderedCech.ZeroGluing
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cochain.ZeroCycles

/-! # Model Global Sections -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cech.ModelGlobalSections.CechModelSections

noncomputable section

/-! The first differential kernel of a Cech model identifies with actual global sections, with its cochain coordinates verified. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite
universe u
variable {X : Scheme.{u}} {R : Type u} [CommRing R]
variable (c : R →+* Γ(X, ⊤)) (M : X.Modules)
variable {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) (hU : iSup U = ⊤)
variable {D : CochainComplex (ModuleCat.{u} R) ℕ}
variable (φ : D ⟶ Ordered.CoefficientCechComplex.orderedCoefficientCechComplex c M U) [QuasiIsoAt φ 0]

def equiv : (D.d 0 1).hom.ker ≃ₗ[R] (Coefficient.ModulePresheaf.coefficientModulePresheaf c M).obj (op ⊤) :=
  (Cochain.ZeroCycles.CochainZeroCycles.kernelEquiv φ).trans (OrderedCech.ZeroGluing.OrderedCechZeroCoordinates.sectionsEquiv c M U hU).symm

theorem coordinate (x : (D.d 0 1).hom.ker) :
    φ.f 0 x.val = OrderedCech.Augmentation.orderedCechSectionMap c M U 0 (equiv c M U hU φ x) := by
  let e := OrderedCech.ZeroGluing.OrderedCechZeroCoordinates.sectionsEquiv c M U hU
  let k := Cochain.ZeroCycles.CochainZeroCycles.kernelEquiv φ
  have he := congrArg Subtype.val (e.apply_symm_apply (k x))
  exact (Cochain.ZeroCycles.CochainZeroCycles.kernelEquiv_apply_val φ x).symm.trans he.symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cech.ModelGlobalSections.CechModelSections
