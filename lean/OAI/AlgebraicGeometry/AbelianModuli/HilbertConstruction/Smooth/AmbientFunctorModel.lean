import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Smooth.AffineFunctorDescent
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.FunctorBaseChange
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.DiagramBaseChangeComposition

/-! # Ambient Functor Model -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Smooth.AmbientFunctorModel

noncomputable section

/-! Smooth recovered ambient charts can be modeled over a common finite coefficient ring. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u v w

structure SmoothAmbientFunctorModel
    {R : Type u} [CommRing R] (C : Subalgebra ℤ R)
    {J : Type v} [Category.{w} J] (G : J ⥤ Over (Spec (.of C))) where
  coefficients : Subalgebra ℤ R
  above : C ≤ coefficients
  finiteType : Algebra.FiniteType ℤ coefficients
  source : J ⥤ Over (Spec (.of coefficients))
  affine : ∀ i, IsAffine (source.obj i).left
  smooth : ∀ i, Smooth (source.obj i).hom
  openImmersion : ∀ {i j} (f : i ⟶ j), IsOpenImmersion (source.map f).left
  recovery : source ⋙ Over.pullback (Spec.map (CommRingCat.ofHom coefficients.val.toRingHom)) ≅
    (G ⋙ Over.pullback (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion above).toRingHom))) ⋙
      Over.pullback (Spec.map (CommRingCat.ofHom coefficients.val.toRingHom))

theorem exists_smoothAmbientFunctorModel
    {R : Type u} [CommRing R] (C : Subalgebra ℤ R) [Algebra.FiniteType ℤ C]
    {J : Type v} [Category.{w} J] [Finite J] [Quiver.IsThin J]
    (G : J ⥤ Over (Spec (.of C))) [∀ i, IsAffine (G.obj i).left]
    [∀ {i j} (f : i ⟶ j), IsOpenImmersion (G.map f).left]
    [∀ i, Smooth ((G ⋙ Over.pullback (Spec.map (CommRingCat.ofHom C.val.toRingHom))).obj i).hom] :
    Nonempty (SmoothAmbientFunctorModel C G) := by
  let c := Spec.map (CommRingCat.ofHom C.val.toRingHom)
  have (i : J) : IsAffine ((G ⋙ Over.pullback c).obj i).left := Affine.FunctorBaseChange.affineFunctorBaseChange_affine G c i
  have {i j : J} (f : i ⟶ j) : IsOpenImmersion ((G ⋙ Over.pullback c).map f).left :=
    Affine.FunctorBaseChange.affineFunctorBaseChange_open G c f
  obtain ⟨D, hCD, hD, F, ha, hs, ho, ⟨e⟩⟩ := AffineFunctorDescent.exists_smooth_affine_functor_model R (G ⋙ Over.pullback c) C
  let d := Spec.map (CommRingCat.ofHom D.val.toRingHom)
  let b := Spec.map (CommRingCat.ofHom (Subalgebra.inclusion hCD).toRingHom)
  have hw : d ≫ b = c := by
    rw [← Spec.map_comp]
    congr 1
  exact ⟨{
    coefficients := D
    above := hCD
    finiteType := hD
    source := F
    affine := ha
    smooth := hs
    openImmersion := ho
    recovery := e ≪≫ (DiagramBaseChangeComposition.diagramBaseChangeCompIso G d b c hw).symm }⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Smooth.AmbientFunctorModel
