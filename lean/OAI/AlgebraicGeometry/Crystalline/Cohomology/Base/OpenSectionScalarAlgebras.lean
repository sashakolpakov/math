import OAI.AlgebraicGeometry.Crystalline.Cohomology.BaseAffine.ReductionRing
import OAI.AlgebraicGeometry.Crystalline.Cohomology.DeRhamPullbackTo

/-! # Open Section Scalar Algebras -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.Base.OpenSectionScalarAlgebras.BaseOpenSectionScalarAlgebras

noncomputable section

/-! Actual section algebras and scalar towers for geometric base change, over arbitrary coefficient universes and on every open. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

section Restriction
variable {R S : Type u} [CommRing R] [CommRing S]
  (ρ : R →+* S) (X : Over (Spec (CommRingCat.of S)))

def restrictBase : Over (Spec (CommRingCat.of R)) :=
  (Over.map (Spec.map (CommRingCat.ofHom ρ))).obj X

theorem sectionBase_comp (U : X.left.Opens) :
    (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫
        (restrictBase ρ X).hom.appLE ⊤ U le_top =
      CommRingCat.ofHom ρ ≫ (Scheme.ΓSpecIso (CommRingCat.of S)).inv ≫
        X.hom.appLE ⊤ U le_top := by
  change (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫
      (X.hom ≫ Spec.map (CommRingCat.ofHom ρ)).appLE ⊤ U _ = _
  rw [← Scheme.Hom.appLE_comp_appLE X.hom (Spec.map (CommRingCat.ofHom ρ))
    ⊤ ⊤ U le_top le_top]
  have htop : (Spec.map (CommRingCat.ofHom ρ)).appLE ⊤ ⊤ le_top =
      (Spec.map (CommRingCat.ofHom ρ)).appTop := by
    simp [Scheme.Hom.appLE, Scheme.Hom.appTop]
    exact Category.comp_id _
  rw [htop, ← Category.assoc, ← Scheme.ΓSpecIso_inv_naturality, Category.assoc]

theorem sectionBaseMap_comp (U : X.left.Opens) :
    AlgebraicForms.AlgebraicDeRham.sectionBaseMap R (restrictBase ρ X) U =
      (AlgebraicForms.AlgebraicDeRham.sectionBaseMap S X U).comp ρ :=
  congrArg (fun f : CommRingCat.of R ⟶ Γ(X.left, U) => f.hom) (sectionBase_comp ρ X U)

end Restriction

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
  (X : Over (Spec (CommRingCat.of R))) (Y : Over (Spec (CommRingCat.of S)))
  (f : Y.left ⟶ X.left) (U : X.left.Opens)

@[instance_reducible] def baseAlgebra : Algebra R Γ(Y.left, f ⁻¹ᵁ U) :=
  ((AlgebraicForms.AlgebraicDeRham.sectionBaseMap S Y (f ⁻¹ᵁ U)).comp (algebraMap R S)).toAlgebra

@[instance_reducible] def sourceAlgebra : Algebra Γ(X.left, U) Γ(Y.left, f ⁻¹ᵁ U) :=
  (f.app U).hom.toAlgebra

local instance : Algebra R Γ(X.left, U) := AlgebraicForms.AlgebraicDeRham.sectionAlgebra R X U
local instance : Algebra S Γ(Y.left, f ⁻¹ᵁ U) := AlgebraicForms.AlgebraicDeRham.sectionAlgebra S Y (f ⁻¹ᵁ U)

theorem sourceTower
    (h : f ≫ X.hom = Y.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap R S))) :
    letI : Algebra R Γ(Y.left, f ⁻¹ᵁ U) := baseAlgebra R S X Y f U
    letI : Algebra Γ(X.left, U) Γ(Y.left, f ⁻¹ᵁ U) := sourceAlgebra R S X Y f U
    IsScalarTower R Γ(X.left, U) Γ(Y.left, f ⁻¹ᵁ U) := by
  let : Algebra R Γ(Y.left, f ⁻¹ᵁ U) := baseAlgebra R S X Y f U
  let : Algebra Γ(X.left, U) Γ(Y.left, f ⁻¹ᵁ U) := sourceAlgebra R S X Y f U
  let g : restrictBase (algebraMap R S) Y ⟶ X := Over.homMk f h
  apply IsScalarTower.of_algebraMap_eq
  intro r
  exact (congrArg (fun φ : R →+* Γ(Y.left, f ⁻¹ᵁ U) => φ r)
    (sectionBaseMap_comp (algebraMap R S) Y (f ⁻¹ᵁ U))).symm.trans
      ((DeRhamPullbackTo.DeRhamPullback.sectionPullback g U).commutes r).symm

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
    (BaseAffine.ReductionRing.BaseAffineReductionRing.ringPushout R S X Y f h U hU)

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.Base.OpenSectionScalarAlgebras.BaseOpenSectionScalarAlgebras
