import OAI.NumberTheory.PadicHodge.GeometricComparison.Affine.OpenBaseChangePushout
import OAI.NumberTheory.PadicHodge.GeometricComparison.ScalarFormsChange
import OAI.NumberTheory.PadicHodge.GeometricComparison.DeRham.Int
import OAI.NumberTheory.PadicHodge.GeometricComparison.Affine.DeRhamScalarExtension

/-! # Open Section Base -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.OpenSectionBase.OpenSectionScalarAlgebras

noncomputable section

/-! Native section algebras and their scalar towers for an actual geometric base-change square. -/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry

variable (R S : Type) [CommRing R] [CommRing S] [Algebra R S]
  (X : Over (Spec (CommRingCat.of R))) (Y : Over (Spec (CommRingCat.of S)))
  (f : Y.left ⟶ X.left) (U : X.left.Opens)

@[instance_reducible] def baseAlgebra : Algebra R Γ(Y.left, f ⁻¹ᵁ U) :=
  ((AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionBaseMap S Y (f ⁻¹ᵁ U)).comp (algebraMap R S)).toAlgebra

@[instance_reducible] def sourceAlgebra : Algebra Γ(X.left, U) Γ(Y.left, f ⁻¹ᵁ U) :=
  (f.app U).hom.toAlgebra

local instance : Algebra R Γ(X.left, U) := AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebra R X U
local instance : Algebra S Γ(Y.left, f ⁻¹ᵁ U) := AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebra S Y (f ⁻¹ᵁ U)

theorem sourceTower
    (h : f ≫ X.hom = Y.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap R S))) :
    letI : Algebra R Γ(Y.left, f ⁻¹ᵁ U) := baseAlgebra R S X Y f U
    letI : Algebra Γ(X.left, U) Γ(Y.left, f ⁻¹ᵁ U) := sourceAlgebra R S X Y f U
    IsScalarTower R Γ(X.left, U) Γ(Y.left, f ⁻¹ᵁ U) := by
  let : Algebra R Γ(Y.left, f ⁻¹ᵁ U) := baseAlgebra R S X Y f U
  let : Algebra Γ(X.left, U) Γ(Y.left, f ⁻¹ᵁ U) := sourceAlgebra R S X Y f U
  let g : ScalarFormsChange.SectionScalarChange.restrictBase (algebraMap R S) Y ⟶ X := Over.homMk f h
  apply IsScalarTower.of_algebraMap_eq
  intro r
  exact (congrArg (fun φ : R →+* Γ(Y.left, f ⁻¹ᵁ U) => φ r)
    (ScalarFormsChange.SectionScalarChange.sectionBaseMap_comp (algebraMap R S) Y (f ⁻¹ᵁ U))).symm.trans
      ((DeRham.Int.sectionPullback g U).commutes r).symm

theorem pushout
    (h : IsPullback f Y.hom X.hom (Spec.map (CommRingCat.ofHom (algebraMap R S))))
    (hU : IsAffineOpen U) :
    letI : Algebra R Γ(Y.left, f ⁻¹ᵁ U) := baseAlgebra R S X Y f U
    letI : Algebra Γ(X.left, U) Γ(Y.left, f ⁻¹ᵁ U) := sourceAlgebra R S X Y f U
    letI : IsScalarTower R S Γ(Y.left, f ⁻¹ᵁ U) := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    letI : IsScalarTower R Γ(X.left, U) Γ(Y.left, f ⁻¹ᵁ U) := sourceTower R S X Y f U h.w
    Algebra.IsPushout R S Γ(X.left, U) Γ(Y.left, f ⁻¹ᵁ U) := by
  let : Algebra R Γ(Y.left, f ⁻¹ᵁ U) := baseAlgebra R S X Y f U
  let : Algebra Γ(X.left, U) Γ(Y.left, f ⁻¹ᵁ U) := sourceAlgebra R S X Y f U
  let : IsScalarTower R S Γ(Y.left, f ⁻¹ᵁ U) := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let : IsScalarTower R Γ(X.left, U) Γ(Y.left, f ⁻¹ᵁ U) := sourceTower R S X Y f U h.w
  exact CommRingCat.isPushout_iff_isPushout.mp
    (Affine.OpenBaseChangePushout.AffineOpenBaseChangePushout.isPushout (algebraMap R S) X Y f h U hU)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.OpenSectionBase.OpenSectionScalarAlgebras
