import OAI.AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId
import Mathlib.AlgebraicGeometry.OpenImmersion

/-! # Open Section Presheaf -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.OpenSectionPresheaf.OpenSectionAlgebras

noncomputable section

/-! Actual section algebras and their base coefficients agree under an open immersion over the base. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

universe u

variable {R : Type u} [CommRing R]
  {X Y : Over (Spec (CommRingCat.of R))} (f : X ⟶ Y) [IsOpenImmersion f.left]

def sectionAlgHom (U : X.left.Opens) :
    (OAI.AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebras R Y).obj (op (f.left ''ᵁ U)) →ₐ[R]
      (OAI.AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebras R X).obj (op U) where
  __ := (f.left.appIso U).hom.hom
  commutes' r := by
    change (f.left.appIso U).hom
        ((Y.hom.appLE ⊤ (f.left ''ᵁ U) le_top) ((Scheme.ΓSpecIso (.of R)).inv r)) =
      (X.hom.appLE ⊤ U le_top) ((Scheme.ΓSpecIso (.of R)).inv r)
    have h : Y.hom.appLE ⊤ (f.left ''ᵁ U) le_top ≫ (f.left.appIso U).hom =
        X.hom.appLE ⊤ U le_top :=
      (congrArg (fun g => Y.hom.appLE ⊤ (f.left ''ᵁ U) le_top ≫ g) (f.left.appIso_hom' U)).trans
        ((Scheme.Hom.appLE_comp_appLE f.left Y.hom ⊤ (f.left ''ᵁ U) U
          le_top (f.left.preimage_image_eq U).ge).trans
            (congrArg (fun g : X.left ⟶ Spec (.of R) => g.appLE ⊤ U le_top) (Over.w f)))
    exact ConcreteCategory.congr_hom h ((Scheme.ΓSpecIso (.of R)).inv r)

def sectionAlgIso (U : X.left.Opens) :
    (OAI.AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebras R Y).obj (op (f.left ''ᵁ U)) ≅
      (OAI.AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebras R X).obj (op U) :=
  CommAlgCat.isoMk (AlgEquiv.ofBijective (sectionAlgHom f U)
    (ConcreteCategory.bijective_of_isIso (f.left.appIso U).hom))

def presheafIso : f.left.opensFunctor.op ⋙ OAI.AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebras R Y ≅
    OAI.AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebras R X :=
  NatIso.ofComponents (fun U => sectionAlgIso f U.unop) (by
    intro U V i
    apply CommAlgCat.hom_ext
    apply AlgHom.ext
    intro a
    exact ConcreteCategory.congr_hom (f.left.appIso_hom_naturality i) a)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.OpenSectionPresheaf.OpenSectionAlgebras
