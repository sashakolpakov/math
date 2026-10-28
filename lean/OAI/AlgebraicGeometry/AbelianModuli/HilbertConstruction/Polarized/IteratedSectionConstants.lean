import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polarized.NoetherianUniversalFunctions
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.BaseChangeFunctor

/-! # Iterated Section Constants -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Every section of every iterated base change of a polarized family over a locally Noetherian base identifies the actual global-function rings. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u

variable {S : Scheme.{u}} [IsLocallyNoetherian S] {g N : ℕ} {δ : Fin g → ℕ}
variable (A : PolarizationData.PolarizedAbelianWithFullLevel g δ N S)

theorem PolarizationData.PolarizedAbelianWithFullLevel.iteratedBaseChangeSection_globalFunctions_isIso
    {T Y : Scheme.{u}} {a : Y ⟶ A.abelian.scheme.left} {q : Y ⟶ T} {t : T ⟶ S}
    (H : IsPullback a q A.abelian.scheme.hom t)
    (y : T ⟶ Y) (hy : y ≫ q = 𝟙 _) (U : Over T) :
    IsIso ((Section.BaseChangeFunctor.familyBaseChangeSection q y hy).app U).left.appTop := by
  have H' : IsPullback (Limits.pullback.snd U.hom q ≫ a) (Limits.pullback.fst U.hom q)
      A.abelian.scheme.hom (U.hom ≫ t) := (IsPullback.of_hasPullback U.hom q).flip.paste_horiz H
  have : IsIso (Limits.pullback.fst U.hom q).appTop :=
    A.cartesian_globalFunctions_isIso_of_locallyNoetherian H'
  exact Proper.FieldBaseChangeConstants.section_globalFunctions_isIso (Limits.pullback.fst U.hom q)
    ((Section.BaseChangeFunctor.familyBaseChangeSection q y hy).app U).left (Section.BaseChangeFunctor.familyBaseChangeSection_fst q y hy U)

theorem PolarizationData.PolarizedAbelianWithFullLevel.iteratedBaseChangeSection_globalFunctions_bijective
    {T Y : Scheme.{u}} {a : Y ⟶ A.abelian.scheme.left} {q : Y ⟶ T} {t : T ⟶ S}
    (H : IsPullback a q A.abelian.scheme.hom t)
    (y : T ⟶ Y) (hy : y ≫ q = 𝟙 _) (U : Over T) :
    Function.Bijective ((Section.BaseChangeFunctor.familyBaseChangeSection q y hy).app U).left.appTop := by
  have := A.iteratedBaseChangeSection_globalFunctions_isIso H y hy U
  exact ConcreteCategory.bijective_of_isIso _

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
