import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LocallyNoetherian.PointedDualHom
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Base.ChangedPolarizedPoincareCompatibility
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Moduli.Isomorphisms

/-! # Canonical Dual -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Canonical dual comparison completes a polarization- and level-preserving group isomorphism on every base change of fixed locally Noetherian polarized families. All dual projectivity and Poincare compatibility are constructed. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj
universe u

variable {S : Scheme.{u}} [IsLocallyNoetherian S] {g N : ℕ} {δ : Fin g → ℕ}
variable (A B : PolarizationData.PolarizedAbelianWithFullLevel g δ N S) (hδ : ∀ i, 0 < δ i) (T : Over S)

include hδ in
theorem LocallyNoetherian.CanonicalDual.baseChangedCanonicalDual_isMonHom_of_locallyNoetherian
    (e : (A.pullback T.hom).abelian.scheme ≅ (B.pullback T.hom).abelian.scheme) [IsMonHom e.hom] :
    IsMonHom (((A.pullback T.hom).dual.familyComparisonIso (B.pullback T.hom).dual e).hom) := by
  exact LocallyNoetherian.PointedDualHom.baseChangedPointedDualMap_isMonHom_of_locallyNoetherian A B hδ T _
    ((A.pullback T.hom).dual.familyComparisonIso_preserves_unit (B.pullback T.hom).dual e)

def Moduli.Isomorphisms.LevelPreservingIso.ofCanonicalDual_locallyNoetherianBaseChange
    (e : (A.pullback T.hom).abelian.scheme ≅ (B.pullback T.hom).abelian.scheme) [IsMonHom e.hom]
    (hp : (A.pullback T.hom).polarization.isogeny.hom ≫
        ((A.pullback T.hom).dual.familyComparisonIso (B.pullback T.hom).dual e).hom =
      e.hom ≫ (B.pullback T.hom).polarization.isogeny.hom)
    (hl : ∀ (V : Over T.left)
      (c : LocallyConstant V.left (Multiplicative (Fin (2 * g) → ZMod N))),
      ((A.pullback T.hom).level.hom.app (.op V) c).val ≫ e.hom =
        ((B.pullback T.hom).level.hom.app (.op V) c).val) :
    Moduli.Isomorphisms.LevelPreservingIso (A.pullback T.hom) (B.pullback T.hom) where
  abelian := e
  dual := (A.pullback T.hom).dual.familyComparisonIso (B.pullback T.hom).dual e
  abelianGroup := inferInstance
  dualGroup := LocallyNoetherian.CanonicalDual.baseChangedCanonicalDual_isMonHom_of_locallyNoetherian A B hδ T e
  polarization := hp
  poincare := A.baseChanged_familyComparisonIso_poincare B T.hom e
  level := hl

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
