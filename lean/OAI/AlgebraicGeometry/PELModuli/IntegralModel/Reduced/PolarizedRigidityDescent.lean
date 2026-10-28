import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Finite.EtaleReduced
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.PEL.RelativePullback
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Pure.AutomorphismDescent

/-! # Polarized Rigidity Descent -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Reduced.PolarizedRigidityDescent

noncomputable section

/-! Rigidity on reduced base tests descends through an actual finite
etale cover and persists after arbitrary parameter pullback. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable {S T : Scheme.{0}} {g N : ℕ} {δ : Fin g → ℕ}

theorem reduced_polarized_rigidity_pullback (A : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N S)
    (hA : ∀ (V : Scheme.{0}) [IsReduced V] (t : V ⟶ S)
      (e : AbelianModuli.HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso (A.pullback t) (A.pullback t)),
      e.abelian.hom = 𝟙 (A.abelian.pullback t).scheme)
    (f : T ⟶ S) (V : Scheme.{0}) [IsReduced V] (t : V ⟶ T)
    (e : AbelianModuli.HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso ((A.pullback f).pullback t) ((A.pullback f).pullback t)) :
    e.abelian.hom = 𝟙 ((A.abelian.pullback f).pullback t).scheme :=
  AbelianModuli.ReferenceFamily.Pure.AutomorphismDescent.pure_abelian_eq_id_via e (AbelianModuli.HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso.pullbackComp A f t) (hA V (t ≫ f))

theorem reduced_polarized_rigidity_of_cover (A : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N S)
    (u : T ⟶ S) [IsFinite u] [Etale u] [Surjective u]
    (B : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N T) (c : AbelianModuli.HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso B (A.pullback u))
    (hB : ∀ (V : Scheme.{0}) [IsReduced V] (t : V ⟶ T)
      (e : AbelianModuli.HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso (B.pullback t) (B.pullback t)),
      e.abelian.hom = 𝟙 (B.abelian.pullback t).scheme)
    (V : Scheme.{0}) [IsReduced V] (t : V ⟶ S)
    (e : AbelianModuli.HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso (A.pullback t) (A.pullback t)) :
    e.abelian.hom = 𝟙 (A.abelian.pullback t).scheme := by
  let W := pullback u t
  let p := pullback.fst u t
  let q := pullback.snd u t
  have : IsReduced W := Finite.EtaleReduced.finite_etale_isReduced q
  let d : AbelianModuli.HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso (B.pullback p) ((A.pullback t).pullback q) :=
    (c.pullback p).trans ((AbelianModuli.HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso.pullbackComp A u p).trans
      ((AbelianModuli.ReferenceFamily.Pure.RelativeLevelIso.purePullbackCongrIso A (p ≫ u) (q ≫ t) pullback.condition).trans
        (AbelianModuli.HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso.pullbackComp A t q).symm))
  have he := AbelianModuli.ReferenceFamily.Pure.AutomorphismDescent.pure_abelian_eq_id_via (e.pullback q) d.symm (hB W p)
  apply (Over.pullback q).map_injective
  exact he.trans ((Over.pullback q).map_id _).symm

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Reduced.PolarizedRigidityDescent
