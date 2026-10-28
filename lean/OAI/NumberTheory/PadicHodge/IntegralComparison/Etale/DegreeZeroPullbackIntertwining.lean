import OAI.NumberTheory.PadicHodge.IntegralComparison.Etale.DegreeZeroGeneralPullback

/-! # Degree Zero Pullback Intertwining -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Etale.DegreeZeroPullbackIntertwining

noncomputable section

/-! Actual rational étale degree-zero pullback intertwines commuting original scheme automorphisms. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

universe u

variable {X Y : Scheme.{u}} [NoetherianSpace X] [NoetherianSpace Y]
  (g : X ⟶ Y) (eX : X ≅ X) (eY : Y ≅ Y) (h : g ≫ eY.hom = eX.hom ≫ g)

include h in
omit [NoetherianSpace X] [NoetherianSpace Y] in
theorem components (c : _root_.ConnectedComponents X) :
    Etale.ConnectedComponents.permutation Y eY (ConnectedComponentSections.map g.base.hom c) =
      ConnectedComponentSections.map g.base.hom (Etale.ConnectedComponents.permutation X eX c) := by
  obtain ⟨x, rfl⟩ := _root_.ConnectedComponents.surjective_coe c
  change _root_.ConnectedComponents.mk (eY.hom (g x)) = _root_.ConnectedComponents.mk (g (eX.hom x))
  exact congrArg _root_.ConnectedComponents.mk (congrArg (fun f : X ⟶ Y => f x) h)

variable (ℓ : ℕ) [Fact ℓ.Prime]

include h in
theorem cohomology (z : Cohomology.RationalEllAdicCohomology ℓ Y 0) :
    PeriodInvariants.BigEtaleCohomology.pullbackQp ℓ g 0 (Etale.ConnectedComponents.endomorphism ℓ Y eY z) =
      Etale.ConnectedComponents.endomorphism ℓ X eX (PeriodInvariants.BigEtaleCohomology.pullbackQp ℓ g 0 z) := by
  apply (Etale.ConnectedComponents.equiv ℓ X).injective
  funext c
  exact (DegreeZeroGeneralPullback.pullback_components ℓ g
    (Etale.ConnectedComponents.endomorphism ℓ Y eY z) c).trans
    ((Etale.ConnectedComponents.pullback ℓ Y eY z (ConnectedComponentSections.map g.base.hom c)).trans
      ((congrArg (Etale.ConnectedComponents.equiv ℓ Y z) (components g eX eY h c)).trans
        ((DegreeZeroGeneralPullback.pullback_components ℓ g z
          (Etale.ConnectedComponents.permutation X eX c)).symm.trans
            (Etale.ConnectedComponents.pullback ℓ X eX (PeriodInvariants.BigEtaleCohomology.pullbackQp ℓ g 0 z) c).symm)))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Etale.DegreeZeroPullbackIntertwining
