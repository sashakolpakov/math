import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Hilbert.Functor

/-! # Identity Parameter Ideal Recovery -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.IdentityParameterIdealRecovery

noncomputable section

/-! Ideal pullback over the identity parameter is the actual source projection on every over-scheme test. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

def overProductSourceMap {S : Scheme.{u}} (X T : Over S) : (T ⨯ X).left ⟶ X.left :=
  (prod.snd : T ⨯ X ⟶ X).left

theorem overProductSourceMap_natural {S : Scheme.{u}} (X : Over S) {T U : Over S} (a : T ⟶ U) :
    HilbertScheme.Presentations.Hilbert.Functor.ambientMap X a ≫ overProductSourceMap X U = overProductSourceMap X T := by
  change ((prod.map a (𝟙 X)) ≫ (prod.snd : U ⨯ X ⟶ X)).left = (prod.snd : T ⨯ X ⟶ X).left
  rw [prod.map_snd, Category.comp_id]

theorem identityParameter_ideal_recovery {S : Scheme.{u}} (X : Over S)
    (I : X.left.IdealSheafData) (T : Over S) :
    (I.comap (overProductSourceMap X (Over.mk (𝟙 S)))).comap
      (HilbertScheme.Presentations.Hilbert.Functor.ambientMap X (Over.mkIdTerminal.from T)) =
        I.comap (overProductSourceMap X T) :=
  (I.comap_comp _ _).symm.trans (congrArg (fun a => I.comap a) (overProductSourceMap_natural X _))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.IdentityParameterIdealRecovery
