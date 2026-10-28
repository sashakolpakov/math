import OAI.ArithmeticGeometry.Models.SpreadingOut.SmoothComponents
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant

/-! # Generic Faithfulness -/

namespace OAI.ArithmeticGeometry.Models.SpreadingOut.GenericFaithfulness.Construction

noncomputable section

/-! Equality of morphisms between smooth separated models can be checked
on the generic fiber. This will descend group identities after the operations
have been spread out. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

theorem spec_injective_schematically_dominant
    {R K : Type u} [CommRing R] [Field K] [IsReduced R]
    (φ : R →+* K) (hφ : Function.Injective φ) :
    IsSchemeTheoreticallyDominant (Spec.map (CommRingCat.ofHom φ)) := by
  have : IsDominant (Spec.map (CommRingCat.ofHom φ)) := by
    constructor
    apply (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical φ).mpr
    rw [(RingHom.injective_iff_ker_eq_bot φ).mp hφ]
    exact bot_le
  exact IsSchemeTheoreticallyDominant.of_isDominant _

theorem smooth_model_reduced_of_injective_generic
    {R K : Type u} [CommRing R] [Field K] [IsReduced R]
    (φ : R →+* K) (hφ : Function.Injective φ)
    (X : Over (Spec (.of R))) [Smooth X.hom] : IsReduced X.left := by
  let g := Spec.map (CommRingCat.ofHom φ)
  have : IsSchemeTheoreticallyDominant g := spec_injective_schematically_dominant φ hφ
  have : IsReduced (pullback X.hom g) := SmoothComponents.Construction.smooth_scheme_reduced (pullback.snd X.hom g)
  exact IsSchemeTheoreticallyDominant.isReduced (pullback.fst X.hom g)

theorem generic_pullback_map_injective
    {R K : Type u} [CommRing R] [Field K] [IsReduced R]
    (φ : R →+* K) (hφ : Function.Injective φ)
    {X Y : Over (Spec (.of R))} [Smooth X.hom] [IsSeparated Y.hom] :
    Function.Injective (fun f : X ⟶ Y ↦
      (Over.pullback (Spec.map (CommRingCat.ofHom φ))).map f) := by
  let g := Spec.map (CommRingCat.ofHom φ)
  have : IsSchemeTheoreticallyDominant g := spec_injective_schematically_dominant φ hφ
  have : IsReduced X.left := smooth_model_reduced_of_injective_generic φ hφ X
  intro f a h
  apply Over.OverMorphism.ext
  apply ext_of_isDominant_of_isSeparated Y.hom (f.w.trans a.w.symm)
    (pullback.fst X.hom g)
  have H := congrArg (fun k ↦ k.left ≫ pullback.fst Y.hom g) h
  change ((Over.pullback g).map f).left ≫ pullback.fst Y.hom g =
    ((Over.pullback g).map a).left ≫ pullback.fst Y.hom g at H
  erw [pullback.lift_fst, pullback.lift_fst] at H
  exact H

end

end OAI.ArithmeticGeometry.Models.SpreadingOut.GenericFaithfulness.Construction
