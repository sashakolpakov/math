import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Hilbert.ClosedAmbientNaturality
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Ideal.ContainmentParameterFunctor

/-! # Ambient Ideal Naturality -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Closed.AmbientIdealNaturality

noncomputable section

/-! Closed ambient embeddings preserve and reflect ideal containment,
and pushforward of arbitrary ideal sheaves commutes with parameter base change. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem ideal_map_closed_le_iff {X Y : Scheme.{u}} (j : X ⟶ Y) [IsClosedImmersion j]
    (I J : X.IdealSheafData) : I.map j ≤ J.map j ↔ I ≤ J := by
  constructor
  · intro h
    have hc := Scheme.IdealSheafData.comap_mono j h
    simpa only [ImmersionIdealEmbedding.ideal_comap_map_closed] using hc
  · intro h
    exact Scheme.IdealSheafData.map_mono j h

namespace Hilbert

variable {S : Scheme.{u}} {X Y : Over S} (j : X ⟶ Y) [IsClosedImmersion j.left]

theorem pushforwardIdeal_baseChange {T U : Over S} (a : T ⟶ U) (I : (Hilbert.Functor.ambient X U).IdealSheafData) :
    (I.comap (Hilbert.Functor.ambientMap X a)).map (Hilbert.ClosedAmbientMap.ambientEmbedding j T) =
      (I.map (Hilbert.ClosedAmbientMap.ambientEmbedding j U)).comap (Hilbert.Functor.ambientMap Y a) := by
  let h := (Hilbert.Functor.family_ambient_isPullback X a I).paste_horiz (Hilbert.ClosedAmbientNaturality.ambientEmbedding_baseChange j a)
  change ((I.comap (Hilbert.Functor.ambientMap X a)).subschemeι ≫ Hilbert.ClosedAmbientMap.ambientEmbedding j T).ker =
    (I.subschemeι ≫ Hilbert.ClosedAmbientMap.ambientEmbedding j U).ker.comap (Hilbert.Functor.ambientMap Y a)
  rw [← h.isoPullback_hom_fst, Scheme.Hom.ker_comp_of_isIso,
    Scheme.IdealSheafData.ker_fst_of_isClosedImmersion]

theorem idealContainmentParameter_pushforward_iff {B T : Over S}
    (I J : (Hilbert.Functor.ambient X B).IdealSheafData) (x : T ⟶ B) :
    I.comap (Hilbert.Functor.ambientMap X x) ≤ J.comap (Hilbert.Functor.ambientMap X x) ↔
      (I.map (Hilbert.ClosedAmbientMap.ambientEmbedding j B)).comap (Hilbert.Functor.ambientMap Y x) ≤
        (J.map (Hilbert.ClosedAmbientMap.ambientEmbedding j B)).comap (Hilbert.Functor.ambientMap Y x) := by
  rw [← pushforwardIdeal_baseChange, ← pushforwardIdeal_baseChange]
  exact (ideal_map_closed_le_iff (Hilbert.ClosedAmbientMap.ambientEmbedding j T) _ _).symm

theorem idealContainmentParameter_pushforward_eq {B : Over S} (I J : (Hilbert.Functor.ambient X B).IdealSheafData) :
    Ideal.ContainmentParameterFunctor.Hilbert.idealContainmentParameterSubfunctor Y (I.map (Hilbert.ClosedAmbientMap.ambientEmbedding j B)) (J.map (Hilbert.ClosedAmbientMap.ambientEmbedding j B)) =
      Ideal.ContainmentParameterFunctor.Hilbert.idealContainmentParameterSubfunctor X I J := by
  ext T x
  exact (idealContainmentParameter_pushforward_iff j I J x).symm

end Hilbert

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Closed.AmbientIdealNaturality
