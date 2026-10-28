import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Proper.FieldBaseChangeConstants
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Smooth.Support

/-! # Base Change Functions -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian

noncomputable section

/-! Global functions on every base change of an abelian variety come from the test scheme. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

universe u

variable {K : Type u} [Field K] {g : ℕ} {T : Scheme.{u}}

theorem Schemes.AbelianScheme.pullback_globalFunctions_isIso (A : Schemes.AbelianScheme g (Spec (.of K)))
    (t : T ⟶ Spec (.of K)) : IsIso (A.pullback t).scheme.hom.appTop := by
  have : IsReduced A.scheme.left := A.reduced_overField
  have : ConnectedSpace A.scheme.left := A.connected_overField
  exact Proper.FieldBaseChangeConstants.properField_baseChange_globalFunctions_isIso A.scheme.hom η[A.scheme].left η[A.scheme].w
    (IsPullback.of_hasPullback A.scheme.hom t)

theorem Schemes.AbelianScheme.pullback_zero_globalFunctions_isIso (A : Schemes.AbelianScheme g (Spec (.of K)))
    (t : T ⟶ Spec (.of K)) : IsIso η[(A.pullback t).scheme].left.appTop := by
  have : IsIso (A.pullback t).scheme.hom.appTop := A.pullback_globalFunctions_isIso t
  exact Proper.FieldBaseChangeConstants.section_globalFunctions_isIso (A.pullback t).scheme.hom
    η[(A.pullback t).scheme].left η[(A.pullback t).scheme].w

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian
