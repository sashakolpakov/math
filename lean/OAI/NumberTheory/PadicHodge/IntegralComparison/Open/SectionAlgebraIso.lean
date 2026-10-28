import OAI.NumberTheory.PadicHodge.IntegralComparison.SectionBaseChange
import Mathlib.AlgebraicGeometry.OpenImmersion

/-! # Section Algebra Iso -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Open.SectionAlgebraIso

noncomputable section

/-!
# IntegralComparison: an open immersion identifies the original native section algebras over the base
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

universe u

variable (k : Type u) [CommRing k] (X Y : Over (Spec (CommRingCat.of k)))
  (g : X.left ⟶ Y.left) [IsOpenImmersion g] (hg : g ≫ Y.hom = X.hom)

include hg in
theorem base_hom (U : X.left.Opens) :
    (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ Y.hom.appLE ⊤ (g ''ᵁ U) le_top ≫ (g.appIso U).hom =
      (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ X.hom.appLE ⊤ U le_top := by
  rw [g.appIso_hom', Scheme.Hom.appLE_comp_appLE g Y.hom ⊤ (g ''ᵁ U) U le_top
    (Scheme.Hom.preimage_image_eq g U).ge, hg]

include hg in
theorem base_inv (U : X.left.Opens) (r : k) :
    (g.appIso U).inv (OAI.AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionBaseMap k X U r) =
      OAI.AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionBaseMap k Y (g ''ᵁ U) r := by
  have h := ConcreteCategory.congr_hom (base_hom k X Y g hg U) r
  change (g.appIso U).hom (OAI.AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionBaseMap k Y (g ''ᵁ U) r) =
    OAI.AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionBaseMap k X U r at h
  exact (congrArg (g.appIso U).inv h).symm.trans (Iso.hom_inv_id_apply (g.appIso U) _)

def component (U : X.left.Opens) :
    (OAI.AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebras k X).obj (op U) ≅
      (OAI.AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebras k Y).obj (op (g ''ᵁ U)) :=
  CommAlgCat.isoMk
    { (g.appIso U).symm.commRingCatIsoToRingEquiv with commutes' := base_inv k X Y g hg U }

def iso : OAI.AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebras k X ≅ g.opensFunctor.op ⋙ OAI.AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebras k Y :=
  NatIso.ofComponents (fun U => component k X Y g hg U.unop)
    (by
      intro U V f
      apply CommAlgCat.hom_ext
      apply AlgHom.ext
      intro x
      exact ConcreteCategory.congr_hom (g.appIso_inv_naturality f) x)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Open.SectionAlgebraIso
