import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SubmersiveEtaleCoordinates
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.EtaleDomainReduced
import Mathlib.RingTheory.Smooth.Flat

/-! # Standard Smooth Domain Reduced -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StandardSmoothDomainReduced

noncomputable section

/-! Standard smooth algebras over domains are reduced, using the explicit étale coordinates. -/

universe u v w t

theorem submersivePresentation_domain_isReduced (R : Type u) (S : Type v)
    [CommRing R] [IsDomain R] [CommRing S] [Algebra R S]
    {ι : Type w} {σ : Type t} [Finite σ] (P : Algebra.SubmersivePresentation R S ι σ) :
    IsReduced S := by
  let := SubmersiveSplitGenerators.submersiveFreeVariableAlgebra R S P.map P.val
  have := SubmersiveEtaleCoordinates.submersiveEtaleCoordinates R S P
  exact EtaleDomainReduced.flat_unramified_domain_isReduced (MvPolynomial (SubmersivePolynomialSplit.UnselectedVariables P.map) R) S

theorem standardSmooth_domain_isReduced (R : Type u) (S : Type v)
    [CommRing R] [IsDomain R] [CommRing S] [Algebra R S] [Algebra.IsStandardSmooth R S] :
    IsReduced S := by
  obtain ⟨ι, σ, _, _, ⟨P⟩⟩ := Algebra.IsStandardSmooth.out (R := R) (S := S)
  exact submersivePresentation_domain_isReduced R S P

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StandardSmoothDomainReduced
