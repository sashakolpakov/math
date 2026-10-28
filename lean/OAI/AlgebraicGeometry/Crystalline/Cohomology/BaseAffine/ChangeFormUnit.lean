import OAI.AlgebraicGeometry.Crystalline.Cohomology.Base.OpenSectionScalarAlgebras
import OAI.AlgebraicGeometry.Crystalline.Cohomology.EtalePolynomialTower
import OAI.AlgebraicGeometry.Crystalline.Cohomology.BaseAffine.OpenOrdinaryFormUnit

/-! # Change Form Unit -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.BaseAffine.ChangeFormUnit.BaseAffineBaseChangeFormUnit

noncomputable section

/-! The actual sheafification unit on a base-changed affine coordinate chart is invertible in every form degree. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

open OAI.AlgebraicGeometry.Crystalline.Cohomology.Base.OpenSectionScalarAlgebras.BaseOpenSectionScalarAlgebras
universe u
variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
  (X : Over (Spec (CommRingCat.of R))) (Y : Over (Spec (CommRingCat.of S)))
  (f : Y.left ⟶ X.left)
  (hp : IsPullback f Y.hom X.hom (Spec.map (CommRingCat.ofHom (algebraMap R S))))
  (U : X.left.Opens) (hU : IsAffineOpen U) (σ : Type u) [LinearOrder σ]

local instance sourceCoefficients : Algebra R Γ(X.left, U) := AlgebraicForms.AlgebraicDeRham.sectionAlgebra R X U
variable [Algebra (MvPolynomial σ R) Γ(X.left, U)]
  [IsScalarTower R (MvPolynomial σ R) Γ(X.left, U)]
  [Algebra.Etale (MvPolynomial σ R) Γ(X.left, U)]

include hp hU σ in
theorem forms (n : ℕ) : IsIso ((toSheafify (Opens.grothendieckTopology Y.left)
    (DeRhamGlobalId.DeRhamGlobal.formsPresheaf S Y n)).app (op (f ⁻¹ᵁ U))) := by
  let : Algebra S Γ(Y.left, f ⁻¹ᵁ U) := AlgebraicForms.AlgebraicDeRham.sectionAlgebra S Y (f ⁻¹ᵁ U)
  let : Algebra R Γ(Y.left, f ⁻¹ᵁ U) := Base.OpenSectionScalarAlgebras.BaseOpenSectionScalarAlgebras.baseAlgebra R S X Y f U
  let : Algebra Γ(X.left, U) Γ(Y.left, f ⁻¹ᵁ U) := Base.OpenSectionScalarAlgebras.BaseOpenSectionScalarAlgebras.sourceAlgebra R S X Y f U
  let : IsScalarTower R S Γ(Y.left, f ⁻¹ᵁ U) := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let : IsScalarTower R Γ(X.left, U) Γ(Y.left, f ⁻¹ᵁ U) := Base.OpenSectionScalarAlgebras.BaseOpenSectionScalarAlgebras.sourceTower R S X Y f U hp.w
  let : Algebra.IsPushout R S Γ(X.left, U) Γ(Y.left, f ⁻¹ᵁ U) := Base.OpenSectionScalarAlgebras.BaseOpenSectionScalarAlgebras.pushout R S X Y f U hp hU
  let : IsAffineHom f := MorphismProperty.of_isPullback hp.flip
    (inferInstance : IsAffineHom (Spec.map (CommRingCat.ofHom (algebraMap R S))))
  exact @OpenOrdinaryFormUnit.BaseAffineOpenOrdinaryFormUnit.forms S inferInstance Y (f ⁻¹ᵁ U) (hU.preimage f) σ inferInstance
    (EtalePolynomialTower.EtalePolynomialPushoutCoordinates.coordinateAlgebra R S Γ(X.left, U) Γ(Y.left, f ⁻¹ᵁ U) σ)
    (EtalePolynomialTower.EtalePolynomialPushoutCoordinates.coordinateTower R S Γ(X.left, U) Γ(Y.left, f ⁻¹ᵁ U) σ)
    (EtalePolynomialTower.EtalePolynomialPushoutCoordinates.etale R S Γ(X.left, U) Γ(Y.left, f ⁻¹ᵁ U) σ) n

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.BaseAffine.ChangeFormUnit.BaseAffineBaseChangeFormUnit
