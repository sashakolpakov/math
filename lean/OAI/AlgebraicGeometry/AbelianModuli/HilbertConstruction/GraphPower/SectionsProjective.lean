import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProperFlat.SectionsProjective
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CanonicalGraph.ResidueCohomology

/-! # Sections Projective -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Every positive canonical graph-bundle power has a finite projective module of global sections over a Noetherian affine base at invertible full level at least three. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
universe u

theorem PolarizationData.PolarizedAbelianWithFullLevel.graphBundle_positivePower_sections_finite_projective
    {S : Scheme.{u}} [IsAffine S] [IsNoetherianRing Γ(S, ⊤)]
    {g N : ℕ} {δ : Fin g → ℕ} (A : PolarizationData.PolarizedAbelianWithFullLevel g δ N S)
    (hN : 3 ≤ N) (hunit : IsUnit (N : Γ(S, ⊤))) (m : ℕ) (hm : 0 < m) :
    Module.Finite Γ(S, ⊤) ((Coefficient.ModulePresheaf.coefficientModulePresheaf A.abelian.scheme.hom.appTop.hom
      (A.graphBundle.tensorPower m).sheaf).obj (op ⊤)) ∧
    Module.Projective Γ(S, ⊤) ((Coefficient.ModulePresheaf.coefficientModulePresheaf A.abelian.scheme.hom.appTop.hom
      (A.graphBundle.tensorPower m).sheaf).obj (op ⊤)) :=
  ProperFlat.SectionsProjective.properFlat_sections_finite_projective_of_fiber_H1_vanishing A.abelian.scheme.hom
    (A.graphBundle.tensorPower m)
    (fun x => A.graphBundle_residueFiber_positivePower_cohomology_subsingleton hN hunit x m hm 0)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
