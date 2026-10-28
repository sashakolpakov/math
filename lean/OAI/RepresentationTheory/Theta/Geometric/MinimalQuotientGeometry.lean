import OAI.RepresentationTheory.Theta.Geometric.Affine.QuotientPoints
import OAI.RepresentationTheory.Theta.Geometric.MinimalEquationIdeal
import OAI.RepresentationTheory.Theta.Geometric.Local.AxisCechChart

/-! # Minimal Quotient Geometry -/

namespace OAI.RepresentationTheory.Theta.Geometric.MinimalQuotientGeometry

noncomputable section

/-! The minimal-equation quotient is local, and its actual scheme map
takes its closed point to the closed point of the original affine base. -/

set_option backward.isDefEq.respectTransparency false
open _root_.AlgebraicGeometry _root_.CategoryTheory

universe u
variable (S : Scheme.{u}) [IsAffine S] [IsLocalRing Γ(S, ⊤)]
    {C : ShortComplex (ModuleCat.{u} Γ(S, ⊤))} (P : AlgebraicGeometry.Quotients.FiniteDescent.LocalMinimalShort.Construction.LocalSectionLifting.LocalMinimalShortComplex C)
    {I : Type*} (basis : Module.Basis I Γ(S, ⊤) P.complex.X₂)
    (e : Γ(S, ⊤) ≃ₗ[Γ(S, ⊤)] P.complex.X₁)

theorem minimalQuotient_closedPoint :
    (Affine.QuotientPoints.affineQuotientScheme S (MinimalEquationIdeal.minimalEquationIdeal P basis e)).hom
      (IsLocalRing.closedPoint (Γ(S, ⊤) ⧸ MinimalEquationIdeal.minimalEquationIdeal P basis e)) =
      Local.AxisCechChart.affineLocalClosedPoint S := by
  have : IsLocalHom (Ideal.Quotient.mk (MinimalEquationIdeal.minimalEquationIdeal P basis e)) :=
    IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
  change S.isoSpec.inv (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
    (MinimalEquationIdeal.minimalEquationIdeal P basis e))) (IsLocalRing.closedPoint _)) = _
  rw [Spec_closedPoint]
  rfl

end

end OAI.RepresentationTheory.Theta.Geometric.MinimalQuotientGeometry
