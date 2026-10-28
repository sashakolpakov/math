import OAI.AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId
import OAI.NumberTheory.PadicHodge.GeometricComparison.AlgebraPushout
import Mathlib.AlgebraicGeometry.Morphisms.Flat

/-! # Reduction Ring -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.BaseAffine.ReductionRing.BaseAffineReductionRing

noncomputable section

/-! Actual affine section rings in a geometric base-change square have the extended coefficient kernel, in arbitrary universes. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
  (X : Over (Spec (CommRingCat.of R))) (Y : Over (Spec (CommRingCat.of S)))
  (f : Y.left ⟶ X.left)
  (hp : IsPullback f Y.hom X.hom (Spec.map (CommRingCat.ofHom (algebraMap R S))))
  (U : X.left.Opens) (hU : IsAffineOpen U)

include hp hU in
theorem ringPushout :
    IsPushout (CommRingCat.ofHom (algebraMap R S))
      (CommRingCat.ofHom (AlgebraicForms.AlgebraicDeRham.sectionBaseMap R X U))
      (CommRingCat.ofHom (AlgebraicForms.AlgebraicDeRham.sectionBaseMap S Y (f ⁻¹ᵁ U))) (f.app U) := by
  have hV : f ⁻¹ᵁ U = f ⁻¹ᵁ U ⊓ Y.hom ⁻¹ᵁ ⊤ := by simp
  have hi := isIso_pushoutSection_of_isAffineOpen hp (US := ⊤) (UT := ⊤) (UX := U) (UY := f ⁻¹ᵁ U)
    le_top le_top hV (isAffineOpen_top _) (isAffineOpen_top _) hU
  have h := (isIso_pushoutSection_iff hp (US := ⊤) (UT := ⊤) (UX := U) (UY := f ⁻¹ᵁ U)
    le_top le_top hV).mp hi
  apply h.flip.of_iso (Scheme.ΓSpecIso (CommRingCat.of R)) (Scheme.ΓSpecIso (CommRingCat.of S))
    (Iso.refl _) (Iso.refl _)
  · have ht : (Spec.map (CommRingCat.ofHom (algebraMap R S))).appLE ⊤ ⊤ le_top =
        (Spec.map (CommRingCat.ofHom (algebraMap R S))).appTop := by
      change (Spec.map (CommRingCat.ofHom (algebraMap R S))).appTop ≫
        (Spec (CommRingCat.of S)).presheaf.map (𝟙 _) = _
      rw [(Spec (CommRingCat.of S)).presheaf.map_id, Category.comp_id]
    exact (congrArg (fun a => a ≫ (Scheme.ΓSpecIso (CommRingCat.of S)).hom) ht).trans
      (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (algebraMap R S)))
  · change _ = (Scheme.ΓSpecIso (CommRingCat.of R)).hom ≫
        ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ X.hom.appLE ⊤ U le_top)
    simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp, Iso.refl_hom, Category.comp_id]
  · change _ = (Scheme.ΓSpecIso (CommRingCat.of S)).hom ≫
        ((Scheme.ΓSpecIso (CommRingCat.of S)).inv ≫ Y.hom.appLE ⊤ (f ⁻¹ᵁ U) le_top)
    simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp, Iso.refl_hom, Category.comp_id]
  · simpa only [Iso.refl_hom, Category.comp_id, Category.id_comp] using (f.app_eq_appLE (U := U)).symm

@[instance_reducible] def targetAlgebra : Algebra R Γ(Y.left, f ⁻¹ᵁ U) :=
  ((AlgebraicForms.AlgebraicDeRham.sectionBaseMap S Y (f ⁻¹ᵁ U)).comp (algebraMap R S)).toAlgebra

local instance sourceCoefficients : Algebra R Γ(X.left, U) := AlgebraicForms.AlgebraicDeRham.sectionAlgebra R X U
local instance targetCoefficients : Algebra S Γ(Y.left, f ⁻¹ᵁ U) := AlgebraicForms.AlgebraicDeRham.sectionAlgebra S Y (f ⁻¹ᵁ U)
local instance targetBase : Algebra R Γ(Y.left, f ⁻¹ᵁ U) := targetAlgebra R S X Y f U
local instance reductionAlgebra : Algebra Γ(X.left, U) Γ(Y.left, f ⁻¹ᵁ U) := (f.app U).hom.toAlgebra
local instance baseTower : IsScalarTower R S Γ(Y.left, f ⁻¹ᵁ U) :=
  IsScalarTower.of_algebraMap_eq (fun _ => rfl)

include hp hU in
theorem sourceTower : IsScalarTower R Γ(X.left, U) Γ(Y.left, f ⁻¹ᵁ U) := by
  apply IsScalarTower.of_algebraMap_eq
  intro r
  exact (congrArg (fun a : CommRingCat.of R ⟶ Γ(Y.left, f ⁻¹ᵁ U) => a.hom r)
    (ringPushout R S X Y f hp U hU).w)

include hp hU in
theorem base (r : R) : (f.app U).hom (AlgebraicForms.AlgebraicDeRham.sectionBaseMap R X U r) =
    AlgebraicForms.AlgebraicDeRham.sectionBaseMap S Y (f ⁻¹ᵁ U) (algebraMap R S r) :=
  (congrArg (fun a : CommRingCat.of R ⟶ Γ(Y.left, f ⁻¹ᵁ U) => a.hom r)
    (ringPushout R S X Y f hp U hU).w).symm

variable (hS : Function.Surjective (algebraMap R S))

include hp hU hS in
theorem surjective : Function.Surjective (f.app U).hom := by
  let : IsScalarTower R Γ(X.left, U) Γ(Y.left, f ⁻¹ᵁ U) := sourceTower R S X Y f hp U hU
  let : Algebra.IsPushout R S Γ(X.left, U) Γ(Y.left, f ⁻¹ᵁ U) :=
    CommRingCat.isPushout_iff_isPushout.mp (ringPushout R S X Y f hp U hU)
  exact NumberTheory.PadicHodge.GeometricComparison.AlgebraPushout.AlgebraPushoutReduction.surjective R S Γ(X.left, U) Γ(Y.left, f ⁻¹ᵁ U) hS

include hp hU hS in
theorem kernel : RingHom.ker (f.app U).hom =
    (RingHom.ker (algebraMap R S)).map (AlgebraicForms.AlgebraicDeRham.sectionBaseMap R X U) := by
  let : IsScalarTower R Γ(X.left, U) Γ(Y.left, f ⁻¹ᵁ U) := sourceTower R S X Y f hp U hU
  let : Algebra.IsPushout R S Γ(X.left, U) Γ(Y.left, f ⁻¹ᵁ U) :=
    CommRingCat.isPushout_iff_isPushout.mp (ringPushout R S X Y f hp U hU)
  exact NumberTheory.PadicHodge.GeometricComparison.AlgebraPushout.AlgebraPushoutReduction.kernel R S Γ(X.left, U) Γ(Y.left, f ⁻¹ᵁ U) hS

include hp hU hS in
theorem kernel_principal (r : R) (hr : RingHom.ker (algebraMap R S) = Ideal.span {r}) :
    RingHom.ker (f.app U).hom = Ideal.span {AlgebraicForms.AlgebraicDeRham.sectionBaseMap R X U r} := by
  rw [kernel R S X Y f hp U hU hS, hr, Ideal.map_span, Set.image_singleton]

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.BaseAffine.ReductionRing.BaseAffineReductionRing
