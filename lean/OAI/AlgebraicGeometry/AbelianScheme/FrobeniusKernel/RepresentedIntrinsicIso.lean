import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.RepresentedMorphisms

/-! # Represented Intrinsic Iso -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.RepresentedIntrinsicIso.Construction

noncomputable section

/-! A specified isomorphism of represented commutative fppf sheaves
induces the native group-scheme isomorphism with those exact maps. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.RepresentedMorphisms.Construction.Schemes

variable {S : Scheme} (G H : Grp (Over S)) [IsCommMonObj G.X] [IsCommMonObj H.X]
variable (e : CartierDuality.CommutativeSheavesAb.Construction.Schemes.representedFppfAb S G ≅ CartierDuality.CommutativeSheavesAb.Construction.Schemes.representedFppfAb S H)

def representedNativeGroupIso : G ≅ H := by
  let f := (CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbHomEquiv G H).symm e.hom
  let g := (CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbHomEquiv H G).symm e.inv
  have hf : CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap f = e.hom := (CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbHomEquiv G H).apply_symm_apply e.hom
  have hg : CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap g = e.inv := (CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbHomEquiv H G).apply_symm_apply e.inv
  refine ⟨f, g, ?_, ?_⟩
  · apply (CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbHomEquiv G G).injective
    exact (CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap_comp f g).trans
      ((congrArg₂ (fun a b => a ≫ b) hf hg).trans
        (e.hom_inv_id.trans (CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap_id G).symm))
  · apply (CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbHomEquiv H H).injective
    exact (CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap_comp g f).trans
      ((congrArg₂ (fun a b => a ≫ b) hg hf).trans
        (e.inv_hom_id.trans (CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap_id H).symm))

theorem representedNativeGroupIso_hom :
    CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap (representedNativeGroupIso G H e).hom = e.hom :=
  (CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbHomEquiv G H).apply_symm_apply e.hom

theorem representedNativeGroupIso_inv :
    CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap (representedNativeGroupIso G H e).inv = e.inv :=
  (CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbHomEquiv H G).apply_symm_apply e.inv

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.RepresentedIntrinsicIso.Construction
