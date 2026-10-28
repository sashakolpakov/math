import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.FieldPointCoordinates
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coefficient.ModulePresheaf

/-! # Field Coefficient Identity -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.FieldCoefficientIdentity

noncomputable section

/-! The canonical coordinate algebra of an affine scheme over Spec K carries
exactly the scalar action obtained from its actual structure morphism. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u

theorem schemeCoefficientMap_Spec_map {K : Type u} [CommRing K]
    {X : Scheme.{u}} [IsAffine X] (p : X ⟶ Spec (.of K)) :
    Spec.map (CommRingCat.ofHom (Coefficient.ModulePresheaf.schemeCoefficientMap p)) = X.isoSpec.inv ≫ p := by
  change Spec.map ((Scheme.ΓSpecIso (.of K)).inv ≫ p.appTop) = _
  rw [Spec.map_comp, ← Scheme.isoSpec_Spec_inv]
  exact Scheme.isoSpec_inv_naturality p

theorem affineOverAlgebra_algebraMap {K : Type u} [CommRing K]
    (M : Over (Spec (.of K))) [IsAffine M.left] :
    algebraMap K (OverChartPoints.affineOverAlgebra K M) = Coefficient.ModulePresheaf.schemeCoefficientMap M.hom := by
  change (Spec.fullyFaithful.preimage (M.left.isoSpec.inv ≫ M.hom)).unop.hom = Coefficient.ModulePresheaf.schemeCoefficientMap M.hom
  have h : (Spec.fullyFaithful.preimage (M.left.isoSpec.inv ≫ M.hom)).unop =
      CommRingCat.ofHom (Coefficient.ModulePresheaf.schemeCoefficientMap M.hom) := by
    apply Spec.map_injective
    exact (Spec.fullyFaithful.map_preimage (M.left.isoSpec.inv ≫ M.hom)).trans
      (schemeCoefficientMap_Spec_map M.hom).symm
  exact congrArg CommRingCat.Hom.hom h

def affineOverAlgebraCoefficientEquiv {K : Type u} [CommRing K]
    (M : Over (Spec (.of K))) [IsAffine M.left] :
    let : Algebra K Γ(M.left, ⊤) := (Coefficient.ModulePresheaf.schemeCoefficientMap M.hom).toAlgebra;
    OverChartPoints.affineOverAlgebra K M ≃ₐ[K] Γ(M.left, ⊤) := by
  let : Algebra K Γ(M.left, ⊤) := (Coefficient.ModulePresheaf.schemeCoefficientMap M.hom).toAlgebra
  exact { RingEquiv.refl Γ(M.left, ⊤) with
    commutes' r := DFunLike.congr_fun (affineOverAlgebra_algebraMap M) r }

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.FieldCoefficientIdentity
