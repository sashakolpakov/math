import OAI.NumberTheory.PadicHodge.IntegralComparison.AffineOpen.DeRhamTrace
import OAI.NumberTheory.PadicHodge.IntegralComparison.AffineOpen.DifferentialBasis
import OAI.NumberTheory.PadicHodge.IntegralComparison.IdealSheafPrincipalEquations

/-! # Parameter Differentials -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.FiniteEtale.ParameterDifferentials

noncomputable section

/-! Actual target parameters pull back through a finite étale map
and restrict to source principal opens with their regularity and their
matching differential basis intact. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open scoped TensorProduct
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable (R : Type u) [CommRing R]
  (X Y : Over (Spec (CommRingCat.of R))) (f : Y ⟶ X) [IsFinite f.left] [Etale f.left]
  (U : X.left.Opens) (hU : IsAffineOpen U)

local instance sourceAlgebra : Algebra (IntrinsicDeRham.SectionUnit.Intrinsic.ring R X U) (IntrinsicDeRham.SectionUnit.Intrinsic.ring R Y (f.left ⁻¹ᵁ U)) :=
  AffineOpen.DeRhamTrace.sectionAlgebra R Y X f U
local instance sourceTower : IsScalarTower R (IntrinsicDeRham.SectionUnit.Intrinsic.ring R X U) (IntrinsicDeRham.SectionUnit.Intrinsic.ring R Y (f.left ⁻¹ᵁ U)) :=
  IsScalarTower.of_algebraMap_eq (fun r => ((AlgebraicGeometry.Crystalline.Cohomology.DeRhamPullbackTo.DeRhamPullback.sectionPullback f U).commutes r).symm)

variable {g : ℕ} (t : Fin g → IntrinsicDeRham.SectionUnit.Intrinsic.ring R X U)

def pullback : Fin g → IntrinsicDeRham.SectionUnit.Intrinsic.ring R Y (f.left ⁻¹ᵁ U) := fun j => f.left.app U (t j)

def parameters (z : IntrinsicDeRham.SectionUnit.Intrinsic.ring R Y (f.left ⁻¹ᵁ U)) : Fin g → IntrinsicDeRham.SectionUnit.Intrinsic.ring R Y (Y.left.basicOpen z) :=
  IdealSheafPrincipalEquations.sequence (f.left ⁻¹ᵁ U) z (pullback R X Y f U t)

include hU in
theorem regular (ht : RingTheory.Sequence.IsWeaklyRegular (IntrinsicDeRham.SectionUnit.Intrinsic.ring R X U) (List.ofFn t))
    (z : IntrinsicDeRham.SectionUnit.Intrinsic.ring R Y (f.left ⁻¹ᵁ U)) :
    RingTheory.Sequence.IsWeaklyRegular (IntrinsicDeRham.SectionUnit.Intrinsic.ring R Y (Y.left.basicOpen z))
      (List.ofFn (parameters R X Y f U t z)) := by
  let : Algebra.Etale (IntrinsicDeRham.SectionUnit.Intrinsic.ring R X U) (IntrinsicDeRham.SectionUnit.Intrinsic.ring R Y (f.left ⁻¹ᵁ U)) :=
    AffineOpen.DeRhamTrace.sectionEtale R Y X f U hU
  have hp := ht.of_flat (S := IntrinsicDeRham.SectionUnit.Intrinsic.ring R Y (f.left ⁻¹ᵁ U))
  rw [List.map_ofFn] at hp
  exact IdealSheafPrincipalEquations.weaklyRegular (f.left ⁻¹ᵁ U) (hU.preimage f.left) z
    (pullback R X Y f U t) hp

variable (b : Module.Basis (Fin g) (IntrinsicDeRham.SectionUnit.Intrinsic.ring R X U) Ω[IntrinsicDeRham.SectionUnit.Intrinsic.ring R X U⁄R])

def fullBasis : Module.Basis (Fin g) (IntrinsicDeRham.SectionUnit.Intrinsic.ring R Y (f.left ⁻¹ᵁ U)) Ω[IntrinsicDeRham.SectionUnit.Intrinsic.ring R Y (f.left ⁻¹ᵁ U)⁄R] := by
  letI : Algebra.Etale (IntrinsicDeRham.SectionUnit.Intrinsic.ring R X U) (IntrinsicDeRham.SectionUnit.Intrinsic.ring R Y (f.left ⁻¹ᵁ U)) :=
    AffineOpen.DeRhamTrace.sectionEtale R Y X f U hU
  exact (b.baseChange (IntrinsicDeRham.SectionUnit.Intrinsic.ring R Y (f.left ⁻¹ᵁ U))).map
    (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale R (IntrinsicDeRham.SectionUnit.Intrinsic.ring R X U) (IntrinsicDeRham.SectionUnit.Intrinsic.ring R Y (f.left ⁻¹ᵁ U)))

theorem fullBasis_apply (hb : ∀ j, b j = KaehlerDifferential.D R (IntrinsicDeRham.SectionUnit.Intrinsic.ring R X U) (t j)) (j : Fin g) :
    fullBasis R X Y f U hU b j =
      KaehlerDifferential.D R (IntrinsicDeRham.SectionUnit.Intrinsic.ring R Y (f.left ⁻¹ᵁ U)) (pullback R X Y f U t j) := by
  let : Algebra.Etale (IntrinsicDeRham.SectionUnit.Intrinsic.ring R X U) (IntrinsicDeRham.SectionUnit.Intrinsic.ring R Y (f.left ⁻¹ᵁ U)) :=
    AffineOpen.DeRhamTrace.sectionEtale R Y X f U hU
  rw [fullBasis, Module.Basis.map_apply, Module.Basis.baseChange_apply, hb]
  change KaehlerDifferential.mapBaseChange R (IntrinsicDeRham.SectionUnit.Intrinsic.ring R X U) (IntrinsicDeRham.SectionUnit.Intrinsic.ring R Y (f.left ⁻¹ᵁ U))
    ((1 : IntrinsicDeRham.SectionUnit.Intrinsic.ring R Y (f.left ⁻¹ᵁ U)) ⊗ₜ[IntrinsicDeRham.SectionUnit.Intrinsic.ring R X U] KaehlerDifferential.D R (IntrinsicDeRham.SectionUnit.Intrinsic.ring R X U) (t j)) = _
  rw [KaehlerDifferential.mapBaseChange_tmul, one_smul, KaehlerDifferential.map_D]
  rfl

def principalBasis (z : IntrinsicDeRham.SectionUnit.Intrinsic.ring R Y (f.left ⁻¹ᵁ U)) :
    Module.Basis (Fin g) (IntrinsicDeRham.SectionUnit.Intrinsic.ring R Y (Y.left.basicOpen z)) Ω[IntrinsicDeRham.SectionUnit.Intrinsic.ring R Y (Y.left.basicOpen z)⁄R] :=
  AffineOpen.DifferentialBasis.basis R Y (homOfLE (Y.left.basicOpen_le z))
    (hU.preimage f.left) ((hU.preimage f.left).basicOpen z) (fullBasis R X Y f U hU b)

theorem principalBasis_apply
    (hb : ∀ j, b j = KaehlerDifferential.D R (IntrinsicDeRham.SectionUnit.Intrinsic.ring R X U) (t j))
    (z : IntrinsicDeRham.SectionUnit.Intrinsic.ring R Y (f.left ⁻¹ᵁ U)) (j : Fin g) :
    principalBasis R X Y f U hU b z j =
      KaehlerDifferential.D R (IntrinsicDeRham.SectionUnit.Intrinsic.ring R Y (Y.left.basicOpen z)) (parameters R X Y f U t z j) :=
  AffineOpen.DifferentialBasis.basis_apply R Y (homOfLE (Y.left.basicOpen_le z))
    (hU.preimage f.left) ((hU.preimage f.left).basicOpen z) (fullBasis R X Y f U hU b)
    (pullback R X Y f U t) (fullBasis_apply R X Y f U hU t b hb) j

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.FiniteEtale.ParameterDifferentials
