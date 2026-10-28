import OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicDeRham.SectionRestriction
import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.LinearAlgebra.TensorProduct.Basis

/-! # Differential Basis -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.AffineOpen.DifferentialBasis

noncomputable section

/-! An actual affine-open restriction carries a differential basis to
its base-change basis, with the original restricted coordinates. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

open OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicDeRham.SectionRestriction.IntrinsicUnit

universe u v
variable (R : Type u) [CommRing R] (X : Over (Spec (CommRingCat.of R)))
  {U V : X.left.Opens} (i : V ⟶ U) (hU : IsAffineOpen U) (hV : IsAffineOpen V)
  {σ : Type v} (b : Module.Basis σ (IntrinsicDeRham.SectionUnit.Intrinsic.ring R X U) Ω[IntrinsicDeRham.SectionUnit.Intrinsic.ring R X U⁄R])

def basis : Module.Basis σ (IntrinsicDeRham.SectionUnit.Intrinsic.ring R X V) Ω[IntrinsicDeRham.SectionUnit.Intrinsic.ring R X V⁄R] := by
  letI := IntrinsicDeRham.SectionRestriction.IntrinsicUnit.restrictionAlgebra R X i
  letI := IntrinsicDeRham.SectionRestriction.IntrinsicUnit.restrictionTower R X i
  letI := IntrinsicDeRham.SectionRestriction.IntrinsicUnit.restrictionEtale R X i hU hV
  exact (b.baseChange (IntrinsicDeRham.SectionUnit.Intrinsic.ring R X V)).map
    (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale R (IntrinsicDeRham.SectionUnit.Intrinsic.ring R X U) (IntrinsicDeRham.SectionUnit.Intrinsic.ring R X V))

theorem basis_apply (x : σ → IntrinsicDeRham.SectionUnit.Intrinsic.ring R X U)
    (hx : ∀ j, b j = KaehlerDifferential.D R (IntrinsicDeRham.SectionUnit.Intrinsic.ring R X U) (x j)) (j : σ) :
    basis R X i hU hV b j = KaehlerDifferential.D R (IntrinsicDeRham.SectionUnit.Intrinsic.ring R X V)
      (((AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebras R X).map i.op).hom (x j)) := by
  let := IntrinsicDeRham.SectionRestriction.IntrinsicUnit.restrictionAlgebra R X i
  let := IntrinsicDeRham.SectionRestriction.IntrinsicUnit.restrictionTower R X i
  let := IntrinsicDeRham.SectionRestriction.IntrinsicUnit.restrictionEtale R X i hU hV
  rw [basis, Module.Basis.map_apply, Module.Basis.baseChange_apply, hx]
  exact ((LinearEquiv.symm_apply_eq
    (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale R (IntrinsicDeRham.SectionUnit.Intrinsic.ring R X U) (IntrinsicDeRham.SectionUnit.Intrinsic.ring R X V))).mp
    (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_symm_D_algebraMap
      R (IntrinsicDeRham.SectionUnit.Intrinsic.ring R X U) (IntrinsicDeRham.SectionUnit.Intrinsic.ring R X V) (x j))).symm

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.AffineOpen.DifferentialBasis
