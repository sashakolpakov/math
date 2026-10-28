import OAI.AlgebraicGeometry.Albanese.Construction.GenericFinite
import OAI.AlgebraicGeometry.Albanese.Construction.DominantSmooth
import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.AlgebraicGeometry.Morphisms.Etale

/-! # Etale Generic -/

namespace OAI.AlgebraicGeometry.Albanese.Construction.EtaleGeneric

noncomputable section

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped TensorProduct

/-- For a smooth domain, vanishing of relative differentials in its fraction
field forces them to vanish before localization, since they form a flat module. -/
theorem smooth_etale_of_fraction_unramified
    (R S F : Type*) [CommRing R] [CommRing S] [Field F] [IsDomain S]
    [Algebra R S] [Algebra S F] [Algebra R F] [IsScalarTower R S F]
    [IsFractionRing S F] [Algebra.Smooth R S] [Algebra.FormallyUnramified R F] :
    Algebra.Etale R S := by
  have : Algebra.FormallyEtale S F := Algebra.FormallyEtale.of_isLocalization (nonZeroDivisors S)
  let e := KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale R S F
  have : Subsingleton (F ⊗[S] Ω[S⁄R]) := e.injective.subsingleton
  have : Subsingleton Ω[S⁄R] :=
    (Module.Flat.tensorProduct_mk_injective (R := S) (S := F) (M := Ω[S⁄R])).subsingleton
  exact Algebra.Etale.iff_formallyUnramified_and_smooth.mpr ⟨⟨inferInstance⟩, inferInstance⟩

set_option backward.isDefEq.respectTransparency false in
/-- Generic pullback commutes with taking germs on arbitrary nonempty opens. -/
theorem dominantFunctionFieldMap_germLE
    {X Y : Scheme} [IsIntegral X] [IsIntegral Y] (i : X ⟶ Y) [IsDominant i]
    (U : Y.Opens) (V : X.Opens) [Nonempty U] [Nonempty V] (e : V ≤ i ⁻¹ᵁ U) :
    Y.germToFunctionField U ≫ DominantDimension.dominantFunctionFieldMap i =
      i.appLE U V e ≫ X.germToFunctionField V := by
  simp only [Scheme.germToFunctionField, DominantDimension.dominantFunctionFieldMap,
    TopCat.Presheaf.stalkCongr_hom, ← Category.assoc]
  rw [TopCat.Presheaf.germ_stalkSpecializes]
  rw [i.germ_stalkMap]
  simp [Scheme.Hom.appLE, Category.assoc]

set_option backward.isDefEq.respectTransparency false in
/-- A smooth morphism of integral schemes is étale if its induced
function-field map is formally unramified. -/
theorem smooth_etale_of_generic_unramified
    {X Y : Scheme} [IsIntegral X] [IsIntegral Y] (i : X ⟶ Y) [IsDominant i] [Smooth i]
    (hgeneric : (DominantDimension.dominantFunctionFieldMap i).hom.FormallyUnramified) : Etale i := by
  have : MorphismProperty.RespectsRight @Etale @IsOpenImmersion :=
    ⟨fun _ hg _ hf => by
      let _ := hg
      let _ := hf
      infer_instance⟩
  apply IsZariskiLocalAtSource.iff_exists_resLE.mpr
  intro x
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, _⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (i x)) isOpen_univ
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, e⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hxU (U.2.preimage i.continuous)
  have : Nonempty U := ⟨⟨i x, hxU⟩⟩
  have : Nonempty V := ⟨⟨x, hxV⟩⟩
  have := functionField_isFractionRing_of_isAffineOpen X V hV
  have := functionField_isFractionRing_of_isAffineOpen Y U hU
  have hgerm : (Y.germToFunctionField U).hom.FormallyUnramified :=
    Algebra.FormallyUnramified.of_isLocalization (nonZeroDivisors Γ(Y, U))
  have hcomp : ((X.germToFunctionField V).hom.comp (i.appLE U V e).hom).FormallyUnramified := by
    rw [← CommRingCat.hom_comp, ← dominantFunctionFieldMap_germLE i U V e]
    exact hgerm.comp hgeneric
  have hsmooth := i.smooth_appLE hU hV e
  have hetale : (i.appLE U V e).hom.Etale := by
    algebraize [(i.appLE U V e).hom, (X.germToFunctionField V).hom,
      (X.germToFunctionField V).hom.comp (i.appLE U V e).hom]
    exact smooth_etale_of_fraction_unramified Γ(Y, U) Γ(X, V) X.functionField
  refine ⟨U, V, hxV, e, ?_⟩
  have : IsAffine U := hU
  have : IsAffine V := hV
  rw [HasRingHomProperty.iff_of_isAffine (P := @Etale)]
  exact (RingHom.Etale.respectsIso.arrow_mk_iso_iff (arrowResLEAppIso i U V e)).mpr hetale

/-- A smooth dominant morphism between integral complex varieties of the same
dimension is étale. -/
theorem smooth_etale_of_dimension_eq
    {X Y : Scheme} [IsIntegral X] [IsIntegral Y] (i : X ⟶ Y) [IsDominant i] [Smooth i]
    (f : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f] [LocallyOfFiniteType (i ≫ f)]
    (hd : Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension (i ≫ f) = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension f) : Etale i :=
  smooth_etale_of_generic_unramified i
    (GenericFinite.dominantFunctionField_formallyUnramified_of_dimension_eq i f hd)

end

end OAI.AlgebraicGeometry.Albanese.Construction.EtaleGeneric
