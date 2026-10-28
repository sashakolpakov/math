import OAI.AlgebraicGeometry.Divisors.LineBundles.Affine.SectionNormalCone
import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-! # Scheme Section -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Affine.SchemeSection.BundleCycles.AffineSchemeSection

noncomputable section

/-! # LineBundleCycles: the actual normal-cone isomorphism for an affine smooth scheme section -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable {X Y : Scheme.{0}} (p : Y ⟶ X) (s : X ⟶ Y) (hs : s ≫ p = 𝟙 X)

abbrev baseAlgebra : Algebra Γ(X, ⊤) Γ(Y, ⊤) := p.appTop.hom.toAlgebra
abbrev quotientAlgebra : Algebra Γ(Y, ⊤) Γ(X, ⊤) := s.appTop.hom.toAlgebra

include hs in
theorem section_appTop : p.appTop ≫ s.appTop = 𝟙 Γ(X, ⊤) := by
  rw [← Scheme.Hom.comp_appTop, hs, Scheme.Hom.id_appTop]

include hs in
theorem scalarTower :
    letI := baseAlgebra p
    letI := quotientAlgebra s
    IsScalarTower Γ(X, ⊤) Γ(Y, ⊤) Γ(X, ⊤) := by
  let := baseAlgebra p
  let := quotientAlgebra s
  exact IsScalarTower.of_algebraMap_eq fun a => (ConcreteCategory.congr_hom (section_appTop p s hs) a).symm

variable [IsAffine X] [IsAffine Y] [Smooth p]

theorem sectionRing_smooth :
    letI := baseAlgebra p
    Algebra.Smooth Γ(X, ⊤) Γ(Y, ⊤) :=
  HasRingHomProperty.appTop (P := @Smooth) p inferInstance

include hs in
theorem normalConeSymmetricMap_bijective : Function.Bijective (Normal.ConeSymmetric.BundleCycles.normalConeSymmetricMap (RingHom.ker s.appTop.hom)) := by
  let := baseAlgebra p
  let := quotientAlgebra s
  let := scalarTower p s hs
  let := sectionRing_smooth p
  exact SectionNormalCone.BundleCycles.affineSection_normalConeSymmetricMap_bijective Γ(X, ⊤) Γ(Y, ⊤)

def normalConeEquiv :
    SymmetricAlgebra (Γ(Y, ⊤) ⧸ RingHom.ker s.appTop.hom) (RingHom.ker s.appTop.hom).Cotangent ≃+*
      Normal.Cone.BundleCycles.NormalConeRing (RingHom.ker s.appTop.hom) :=
  RingEquiv.ofBijective (Normal.ConeSymmetric.BundleCycles.normalConeSymmetricMap _) (normalConeSymmetricMap_bijective p s hs)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Affine.SchemeSection.BundleCycles.AffineSchemeSection
