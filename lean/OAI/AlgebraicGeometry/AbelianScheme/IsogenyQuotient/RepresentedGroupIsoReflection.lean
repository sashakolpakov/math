import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.RepresentedMorphisms

/-! # Represented Group Iso Reflection -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.RepresentedGroupIsoReflection.Construction

noncomputable section

/-! An isomorphism of actual represented commutative fppf sheaves
gives an isomorphism of their native group schemes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.RepresentedMorphisms.Construction.Schemes

universe u
variable {S : Scheme.{u}} (G H : Grp (Over S)) [IsCommMonObj G.X] [IsCommMonObj H.X]

def groupIsoOfRepresentedFppfAbIso (e : CartierDuality.CommutativeSheavesAb.Construction.Schemes.representedFppfAb S G ≅ CartierDuality.CommutativeSheavesAb.Construction.Schemes.representedFppfAb S H) : G ≅ H := by
  let f := (CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbHomEquiv G H).symm e.hom
  let g := (CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbHomEquiv H G).symm e.inv
  have hf : CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap f = e.hom := (CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbHomEquiv G H).apply_symm_apply _
  have hg : CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap g = e.inv := (CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbHomEquiv H G).apply_symm_apply _
  refine ⟨f, g, ?_, ?_⟩
  · apply (CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbHomEquiv G G).injective
    change CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap (f ≫ g) = CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap (𝟙 G)
    rw [CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap_comp, hf, hg, e.hom_inv_id, CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap_id]
  · apply (CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbHomEquiv H H).injective
    change CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap (g ≫ f) = CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap (𝟙 H)
    rw [CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap_comp, hg, hf, e.inv_hom_id, CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap_id]

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.RepresentedGroupIsoReflection.Construction
