import OAI.AlgebraicGeometry.Resolution.Blowups.Blowup.Functor
import OAI.AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace

/-! # Complex Naturality -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Affine.ComplexNaturality.Construction

noncomputable section

section

/-! Scalar maps on affine opens induced by the actual complex structure morphism. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {X : Scheme} (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase)

/-- The complex algebra structure on an affine chart, recovered from its structure map. -/
def affineComplexScalars (U : X.affineOpens) : ℂ →+* Γ(X, U) :=
  (Spec.preimage (U.2.fromSpec ≫ f)).hom

theorem affineComplexScalars_spec (U : X.affineOpens) :
    Spec.map (CommRingCat.ofHom (affineComplexScalars f U)) = U.2.fromSpec ≫ f :=
  Spec.map_preimage _

/-- Restricting regular functions respects the actual complex scalar maps. -/
theorem affineComplexScalars_restrict {U V : X.affineOpens} (h : U ≤ V) :
    (Blowup.Functor.Construction.affineRestriction h).comp (affineComplexScalars f V) = affineComplexScalars f U := by
  have he : CommRingCat.ofHom (affineComplexScalars f V) ≫
      CommRingCat.ofHom (Blowup.Functor.Construction.affineRestriction h) = CommRingCat.ofHom (affineComplexScalars f U) := by
    apply Spec.map_injective
    rw [Spec.map_comp, affineComplexScalars_spec, affineComplexScalars_spec,
      ← Category.assoc]
    congr 1
    exact IsAffineOpen.map_fromSpec V.2 U.2 (homOfLE (X := X.Opens) h).op
  exact congrArg CommRingCat.Hom.hom he

end

/-! Complex scalar compatibility for actual affine maps and open-chart identifications. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {X Y : Scheme} (f : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) (g : X ⟶ Y)

/-- Every actual map of affine charts respects the complex scalars
coming from the original structure morphism. -/
theorem affineComplexScalars_appLE (U : X.affineOpens) (V : Y.affineOpens)
    (h : U.1 ≤ g ⁻¹ᵁ V.1) :
    (g.appLE V.1 U.1 h).hom.comp (affineComplexScalars f V) =
      affineComplexScalars (g ≫ f) U := by
  have he : CommRingCat.ofHom (affineComplexScalars f V) ≫ g.appLE V.1 U.1 h =
      CommRingCat.ofHom (affineComplexScalars (g ≫ f) U) := by
    apply Spec.map_injective
    rw [Spec.map_comp, affineComplexScalars_spec, affineComplexScalars_spec,
      ← Category.assoc, IsAffineOpen.SpecMap_appLE_fromSpec g V.2 U.2 h, Category.assoc]
  exact congrArg CommRingCat.Hom.hom he

/-- The affine ring isomorphism furnished by an open immersion is an
isomorphism over the original complex base. -/
theorem affineComplexScalars_appIso [IsOpenImmersion g] (U : X.affineOpens) :
    (g.appIso U.1).hom.hom.comp
        (affineComplexScalars f ⟨g ''ᵁ U.1, U.2.image_of_isOpenImmersion g⟩) =
      affineComplexScalars (g ≫ f) U := by
  rw [Scheme.Hom.appIso_hom']
  exact affineComplexScalars_appLE f g U ⟨g ''ᵁ U.1, U.2.image_of_isOpenImmersion g⟩
    (Scheme.Hom.preimage_image_eq g U.1).ge

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Affine.ComplexNaturality.Construction
