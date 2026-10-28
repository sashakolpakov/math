import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Universal.DualPointedHomomorphism

/-! # Canonical Dual Group -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Universal.CanonicalDualGroup

noncomputable section

/-! Canonical comparisons between arbitrary chosen polarized duals of a
test of a fixed Noetherian projective abelian family preserve its group law. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {S : Scheme.{u}} [IsNoetherian S] {g N : ℕ} {δ : Fin g → ℕ}
variable (A : Abelian.Schemes.AbelianScheme g S) (PA : Projective.ProjectivePresentations.ProjectivePresentation A.scheme) (T : Over S)
variable (D E : Dual.Data.DualAbelianData (A.pullback T.hom)) (p : PolarizationData.Polarization D δ) (q : PolarizationData.Polarization E δ)
variable (l : (A.pullback T.hom).FullLevel N) (hδ : ∀ i, 0 < δ i)

include PA p q l hδ in
theorem universalCanonicalDual_isMonHom : IsMonHom (D.uniqueUnderlyingIso E).hom :=
  DualPointedHomomorphism.universalDual_pointedMap_isMonHom A A PA PA T D E p q l hδ
    (D.uniqueUnderlyingIso E).hom (D.uniqueUnderlyingIso_preserves_unit E)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Universal.CanonicalDualGroup
