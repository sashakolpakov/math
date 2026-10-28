import OAI.RepresentationTheory.Theta.Geometric.GlobalPowerFrameRestriction

/-! # Multilinear Restriction Composition -/

namespace OAI.RepresentationTheory.Theta.Geometric.MultilinearRestrictionComposition

noncomputable section

/-! Native multilinear maps respect the composition comparison for open
restriction. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem multilinear_restrict_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsOpenImmersion f] [IsOpenImmersion g] {L P : Z.Modules} {n : ℕ}
    (β : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.Powers.SheafMultilinearMap L n P) :
    ((β.restrict g).restrict f).precomp ((Scheme.Modules.restrictFunctorComp f g).app L).hom =
      (β.restrict (f ≫ g)).postcomp ((Scheme.Modules.restrictFunctorComp f g).app P).hom := by
  ext U s
  have hU : g ''ᵁ (f ''ᵁ U) = (f ≫ g) ''ᵁ U := by simp
  change (Fin n → Γ(L, (f ≫ g) ''ᵁ U)) at s
  change (β.app (g ''ᵁ (f ''ᵁ U)))
      (fun i => L.presheaf.map (eqToHom hU).op (s i)) =
    P.presheaf.map (eqToHom hU).op (β.app ((f ≫ g) ''ᵁ U) s)
  exact (β.naturality (eqToHom hU) s).symm

end

end OAI.RepresentationTheory.Theta.Geometric.MultilinearRestrictionComposition
