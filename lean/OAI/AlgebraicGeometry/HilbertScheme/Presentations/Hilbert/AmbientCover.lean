import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Hilbert.AmbientProjections
import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic

/-! # Ambient Cover -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Hilbert.AmbientCover

noncomputable section

/-! Native Hilbert ambients preserve the actual overlap pullbacks and open
covers of their test schemes. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u
variable {S : Scheme.{u}} (X : Over S)

theorem ambient_pullback {T U V : Over S} (f : T ⟶ V) (g : U ⟶ V) :
    IsPullback (Functor.ambientMap X (pullback.fst f g)) (Functor.ambientMap X (pullback.snd f g))
      (Functor.ambientMap X f) (Functor.ambientMap X g) := by
  have hc : Functor.ambientMap X (pullback.fst f g) ≫ Functor.ambientMap X f =
      Functor.ambientMap X (pullback.snd f g) ≫ Functor.ambientMap X g := by
    rw [← Functor.ambientMap_comp, ← Functor.ambientMap_comp, pullback.condition]
  have H := (Functor.ambient_isPullback X (pullback.snd f g)).paste_horiz
    ((IsPullback.of_hasPullback f g).map (Over.forget S))
  apply IsPullback.of_right _ hc (Functor.ambient_isPullback X f)
  rw [AmbientProjections.ambientMap_projection, AmbientProjections.ambientMap_projection]
  exact H

theorem ambient_overlap_ideal_compatibility {T U V : Over S} (f : T ⟶ V) (g : U ⟶ V)
    (I : (Functor.ambient X T).IdealSheafData) (J : (Functor.ambient X U).IdealSheafData)
    (h : I.comap (Functor.ambientMap X (pullback.fst f g)) = J.comap (Functor.ambientMap X (pullback.snd f g))) :
    I.comap (pullback.fst (Functor.ambientMap X f) (Functor.ambientMap X g)) =
      J.comap (pullback.snd (Functor.ambientMap X f) (Functor.ambientMap X g)) := by
  let hp := ambient_pullback X f g
  have he := congrArg (fun K => K.comap hp.isoPullback.inv) h
  rwa [← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp,
    hp.isoPullback_inv_fst, hp.isoPullback_inv_snd] at he

instance ambientMap_isOpenImmersion {T U : Over S} (f : T ⟶ U) [IsOpenImmersion f.left] :
    IsOpenImmersion (Functor.ambientMap X f) :=
  MorphismProperty.of_isPullback (Functor.ambient_isPullback X f) inferInstance

def ambientOpenCover {T : Over S} {J : Type u} (U : J → Over S) (f : ∀ i, U i ⟶ T)
    [∀ i, IsOpenImmersion (f i).left]
    (hcover : ∀ t : T.left, ∃ i, ∃ y : (U i).left, (f i).left y = t) : (Functor.ambient X T).OpenCover.{u} where
  I₀ := J
  X i := Functor.ambient X (U i)
  f i := Functor.ambientMap X (f i)
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨?_, inferInstance⟩
    intro z
    obtain ⟨i, y, hy⟩ := hcover (Functor.ambientProjection X T z)
    obtain ⟨w, _, hw⟩ := Scheme.exists_preimage_of_isPullback (Functor.ambient_isPullback X (f i)) y z hy
    exact ⟨i, w, hw⟩

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Hilbert.AmbientCover
