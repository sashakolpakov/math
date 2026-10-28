import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Spec.CoefficientCechComparison
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! # Quotient Coefficient Map -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.QuotientCoefficientMap

noncomputable section

/-! The morphism from a coordinate algebra to an affine scheme induces exactly the prescribed coefficient map. For a quotient, the induced scalar action is the canonical quotient action. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u
variable {S : Scheme.{u}} [IsAffine S] {B : Type u} [CommRing B]

def affineCoordinateMap (φ : Γ(S, ⊤) →+* B) : Spec (.of B) ⟶ S :=
  Spec.map (CommRingCat.ofHom φ) ≫ S.isoSpec.inv

theorem specBaseCoefficientMap_specMap (g : Spec (.of B) ⟶ S) :
    Spec.map (CommRingCat.ofHom (HilbertConstruction.Spec.CoefficientCechComparison.specBaseCoefficientMap g)) = g ≫ S.isoSpec.hom := by
  change Spec.map (g.appTop ≫ (Scheme.ΓSpecIso (.of B)).hom) = _
  exact (Spec.map_comp g.appTop (Scheme.ΓSpecIso (.of B)).hom).trans
    ((congrArg (fun v : Spec (.of B) ⟶ Spec Γ(Spec (.of B), ⊤) => v ≫ Spec.map g.appTop)
      (Scheme.isoSpec_Spec_hom (.of B)).symm).trans (Scheme.isoSpec_hom_naturality g))

theorem specBaseCoefficientMap_affineCoordinateMap (φ : Γ(S, ⊤) →+* B) :
    HilbertConstruction.Spec.CoefficientCechComparison.specBaseCoefficientMap (affineCoordinateMap φ) = φ := by
  have h : CommRingCat.ofHom (HilbertConstruction.Spec.CoefficientCechComparison.specBaseCoefficientMap (affineCoordinateMap φ)) =
      CommRingCat.ofHom φ := by
    apply Spec.map_injective
    exact (specBaseCoefficientMap_specMap (affineCoordinateMap φ)).trans
      ((Category.assoc (Spec.map (CommRingCat.ofHom φ)) S.isoSpec.inv S.isoSpec.hom).trans
        ((congrArg (fun v : Spec Γ(S, ⊤) ⟶ Spec Γ(S, ⊤) => Spec.map (CommRingCat.ofHom φ) ≫ v)
          S.isoSpec.inv_hom_id).trans (Category.comp_id _)))
  exact congrArg (fun v : Γ(S, ⊤) ⟶ CommRingCat.of B => v.hom) h

theorem affineCoordinateMap_isClosedImmersion (φ : Γ(S, ⊤) →+* B)
    (hφ : Function.Surjective φ) : IsClosedImmersion (affineCoordinateMap φ) := by
  have : IsClosedImmersion (Spec.map (CommRingCat.ofHom φ)) :=
    IsClosedImmersion.spec_of_surjective (CommRingCat.ofHom φ) hφ
  change IsClosedImmersion (Spec.map (CommRingCat.ofHom φ) ≫ S.isoSpec.inv)
  infer_instance

theorem affineQuotientCoefficientAlgebra_eq (I : Ideal Γ(S, ⊤)) :
    (HilbertConstruction.Spec.CoefficientCechComparison.specBaseCoefficientMap (affineCoordinateMap (Ideal.Quotient.mk I))).toAlgebra =
      (inferInstance : Algebra Γ(S, ⊤) (Γ(S, ⊤) ⧸ I)) := by
  rw [specBaseCoefficientMap_affineCoordinateMap]
  simpa only [Ideal.Quotient.algebraMap_eq] using
    (toAlgebra_algebraMap (R := Γ(S, ⊤)) (S := Γ(S, ⊤) ⧸ I))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.QuotientCoefficientMap
