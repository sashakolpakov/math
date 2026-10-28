import OAI.AlgebraicGeometry.Quotients.FiniteDescent.SchemeNorm
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.AffineGroupoidIs

/-! # Norm Base Change -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.NormBaseChange.Construction

noncomputable section

/-! The finite-free norm commutes with every actual affine pullback
square. Its base-change basis is constructed from the ring pushout. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u v

theorem schemeNorm_baseChange
    {X Y X' Y' : Scheme.{u}} [IsAffine X] [IsAffine Y] [IsAffine X'] [IsAffine Y']
    (f : X ⟶ Y) (g : X' ⟶ Y') (j : X' ⟶ X) (i : Y' ⟶ Y)
    (hs : IsPullback j g f i) {ι : Type v} [Fintype ι]
    (b : letI := f.appTop.hom.toAlgebra; Module.Basis ι Γ(Y, ⊤) Γ(X, ⊤))
    (a : Γ(X, ⊤)) :
    Quotients.FiniteDescent.SchemeNorm.Construction.SchemeNormOpen.norm g (j.appTop a) =
      i.appTop (Quotients.FiniteDescent.SchemeNorm.Construction.SchemeNormOpen.norm f a) := by
  classical
  obtain ⟨b', hb'⟩ := Quotients.FiniteDescent.AffineGroupoidIs.Construction.AffineGroupoid.exists_basis_of_isPushout
    f.appTop i.appTop j.appTop g.appTop (isPushout_appTop_of_isPullback hs) b
  let := f.appTop.hom.toAlgebra
  let := g.appTop.hom.toAlgebra
  apply Quotients.FiniteDescent.InvariantPolynomialOf.Construction.InvariantPolynomial.norm_map_of_basis i.appTop.hom j.appTop.hom _ b b' hb'
  intro r
  exact congrArg (fun a : X' ⟶ Y => a.appTop r) hs.w

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.NormBaseChange.Construction
