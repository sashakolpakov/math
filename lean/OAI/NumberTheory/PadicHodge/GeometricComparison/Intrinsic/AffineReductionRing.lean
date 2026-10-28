import OAI.NumberTheory.PadicHodge.GeometricComparison.AlgebraPushout
import OAI.NumberTheory.PadicHodge.GeometricComparison.OpenSectionBase

/-! # Affine Reduction Ring -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Intrinsic.AffineReductionRing.IntrinsicAffineReductionRing

noncomputable section

/-! Reduction on the actual rings of affine geometric sections is surjective
with the original extended coefficient kernel. -/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.GeometricComparison.OpenSectionBase.OpenSectionScalarAlgebras

variable (R S : Type) [CommRing R] [CommRing S] [Algebra R S]
  (X : Over (Spec (CommRingCat.of R))) (Y : Over (Spec (CommRingCat.of S)))
  (f : Y.left ⟶ X.left)
  (hp : IsPullback f Y.hom X.hom (Spec.map (CommRingCat.ofHom (algebraMap R S))))
  (U : X.left.Opens) (hU : IsAffineOpen U) (hS : Function.Surjective (algebraMap R S))

local instance sourceCoefficients : Algebra R Γ(X.left, U) := AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebra R X U
local instance targetCoefficients : Algebra S Γ(Y.left, f ⁻¹ᵁ U) :=
  AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebra S Y (f ⁻¹ᵁ U)
local instance targetBase : Algebra R Γ(Y.left, f ⁻¹ᵁ U) := OpenSectionBase.OpenSectionScalarAlgebras.baseAlgebra R S X Y f U
local instance reductionAlgebra : Algebra Γ(X.left, U) Γ(Y.left, f ⁻¹ᵁ U) := OpenSectionBase.OpenSectionScalarAlgebras.sourceAlgebra R S X Y f U
local instance baseTower : IsScalarTower R S Γ(Y.left, f ⁻¹ᵁ U) :=
  IsScalarTower.of_algebraMap_eq (fun _ => rfl)

include hp hU hS in
theorem surjective : Function.Surjective (f.app U).hom := by
  let : IsScalarTower R Γ(X.left, U) Γ(Y.left, f ⁻¹ᵁ U) := OpenSectionBase.OpenSectionScalarAlgebras.sourceTower R S X Y f U hp.w
  let : Algebra.IsPushout R S Γ(X.left, U) Γ(Y.left, f ⁻¹ᵁ U) := OpenSectionBase.OpenSectionScalarAlgebras.pushout R S X Y f U hp hU
  exact AlgebraPushout.AlgebraPushoutReduction.surjective R S Γ(X.left, U) Γ(Y.left, f ⁻¹ᵁ U) hS

include hp hU hS in
theorem kernel : RingHom.ker (f.app U).hom =
    (RingHom.ker (algebraMap R S)).map (AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionBaseMap R X U) := by
  let : IsScalarTower R Γ(X.left, U) Γ(Y.left, f ⁻¹ᵁ U) := OpenSectionBase.OpenSectionScalarAlgebras.sourceTower R S X Y f U hp.w
  let : Algebra.IsPushout R S Γ(X.left, U) Γ(Y.left, f ⁻¹ᵁ U) := OpenSectionBase.OpenSectionScalarAlgebras.pushout R S X Y f U hp hU
  exact AlgebraPushout.AlgebraPushoutReduction.kernel R S Γ(X.left, U) Γ(Y.left, f ⁻¹ᵁ U) hS

include hp hU hS in
theorem kernel_principal (r : R) (hr : RingHom.ker (algebraMap R S) = Ideal.span {r}) :
    RingHom.ker (f.app U).hom = Ideal.span {AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionBaseMap R X U r} := by
  rw [kernel R S X Y f hp U hU hS, hr, Ideal.map_span, Set.image_singleton]

include hp in
theorem base (r : R) : (f.app U).hom (AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionBaseMap R X U r) =
    AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionBaseMap S Y (f ⁻¹ᵁ U) (algebraMap R S r) := by
  let : IsScalarTower R Γ(X.left, U) Γ(Y.left, f ⁻¹ᵁ U) := OpenSectionBase.OpenSectionScalarAlgebras.sourceTower R S X Y f U hp.w
  exact (IsScalarTower.algebraMap_apply R Γ(X.left, U) Γ(Y.left, f ⁻¹ᵁ U) r).symm

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Intrinsic.AffineReductionRing.IntrinsicAffineReductionRing
