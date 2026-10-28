import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Level.MorphismPreservationParameters

/-! # Preservation Properties -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Level.PreservationProperties

noncomputable section

/-! Named full-level preservation properties package the same all-test-scheme condition and its arbitrary base changes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

def FullLevelPreserves {S : Scheme.{u}} {g N : ℕ} {A B : Abelian.Schemes.AbelianScheme g S}
    (l : A.FullLevel N) (k : B.FullLevel N) (f : A.scheme ⟶ B.scheme) : Prop :=
  ∀ (T : Over S) (c : LocallyConstant T.left (Multiplicative (Fin (2 * g) → ZMod N))),
    (l.hom.app (.op T) c).val ≫ f = (k.hom.app (.op T) c).val

def FullLevelPreservesPullback {S T : Scheme.{u}} {g N : ℕ} {A B : Abelian.Schemes.AbelianScheme g S}
    (l : A.FullLevel N) (k : B.FullLevel N) (f : A.scheme ⟶ B.scheme) (b : T ⟶ S) : Prop :=
  FullLevelPreserves (l.pullback b) (k.pullback b) ((Over.pullback b).map f)

theorem fullLevelParameter_factor_preserves
    {S : Scheme.{u}} (M : Over S) [IsLocallyNoetherian M.left]
    {g N : ℕ} [NeZero N] (A B : Abelian.Schemes.AbelianScheme g M.left)
    (l : A.FullLevel N) (k : B.FullLevel N) (f : A.scheme ⟶ B.scheme)
    {T : Over S} (a : T ⟶ MorphismPreservationParameters.fullLevelMorphismPreservingParameter M A B l k f) :
    FullLevelPreservesPullback l k f (a ≫ MorphismPreservationParameters.fullLevelMorphismPreservingParameterInclusion M A B l k f).left :=
  (MorphismPreservationParameters.fullLevelMorphismPreservingParameterPointEquiv M A B l k f T a).property

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Level.PreservationProperties
