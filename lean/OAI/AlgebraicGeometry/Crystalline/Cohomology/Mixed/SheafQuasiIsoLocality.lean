import OAI.AlgebraicGeometry.Crystalline.Cohomology.MixedCech.SheafExactness
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels

/-! # Sheaf Quasi Iso Locality -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.Mixed.SheafQuasiIsoLocality.MixedSheafQuasiIsoLocality

noncomputable section

/-!
Mixed-universe version for the native crystalline coefficient modules.

# Detecting cohomology isomorphisms on an open cover

Open restriction is exact. Its kernels and cokernels therefore detect
isomorphisms using the vanishing criterion for sheaves on a cover.
-/

open _root_.CategoryTheory Limits Opposite _root_.AlgebraicGeometry

universe u v

variable (R : Type v) [CommRing R] (X : Scheme.{u})
  {ι : Type u} (U : ι → X.Opens) (hU : iSup U = ⊤)

abbrev Sheaves := Sheaf (Opens.grothendieckTopology X) (ModuleCat.{max u v} R)

include hU in
theorem kernel_isZero_of_restriction_isIso {A B : Sheaves R X} (f : A ⟶ B)
    (hf : ∀ i, IsIso ((MixedCech.CechRestriction.MixedCechRestriction.sheafRestrictionFunctor R (U i).ι).map f)) :
    IsZero (kernel f) := by
  apply SheafLocality.MixedSheafLocality.isZero_of_restrictions R X U hU
  intro i
  let G := MixedCech.CechRestriction.MixedCechRestriction.sheafRestrictionFunctor R (U i).ι
  have : IsIso (G.map f) := hf i
  exact (isZero_kernel_of_mono (G.map f)).of_iso (PreservesKernel.iso G f)

include hU in
theorem cokernel_isZero_of_restriction_isIso {A B : Sheaves R X} (f : A ⟶ B)
    (hf : ∀ i, IsIso ((MixedCech.CechRestriction.MixedCechRestriction.sheafRestrictionFunctor R (U i).ι).map f)) :
    IsZero (cokernel f) := by
  apply SheafLocality.MixedSheafLocality.isZero_of_restrictions R X U hU
  intro i
  let G := MixedCech.CechRestriction.MixedCechRestriction.sheafRestrictionFunctor R (U i).ι
  have : IsIso (G.map f) := hf i
  exact (isZero_cokernel_of_epi (G.map f)).of_iso (PreservesCokernel.iso G f)

include hU in
/-- A morphism of module sheaves is an isomorphism if it is so on an open cover. -/
theorem isIso_of_restrictions {A B : Sheaves R X} (f : A ⟶ B)
    (hf : ∀ i, IsIso ((MixedCech.CechRestriction.MixedCechRestriction.sheafRestrictionFunctor R (U i).ι).map f)) :
    IsIso f := by
  have : Mono f := Abelian.mono_of_kernel_ι_eq_zero f
    ((kernel_isZero_of_restriction_isIso R X U hU f hf).eq_of_src _ _)
  have : Epi f := Abelian.epi_of_cokernel_π_eq_zero f
    ((cokernel_isZero_of_restriction_isIso R X U hU f hf).eq_of_tgt _ _)
  exact isIso_of_mono_of_epi f

section General

variable {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
  (G : A ⥤ B) [G.Additive] [G.PreservesHomology]
  {K L : CochainComplex A ℕ} (f : K ⟶ L) (n : ℕ)

theorem map_homologyMap_isIso
    [QuasiIsoAt ((G.mapHomologicalComplex (ComplexShape.up ℕ)).map f) n] :
    IsIso (G.map (HomologicalComplex.homologyMap f n)) := by
  have h := ShortComplex.mapHomologyIso_hom_naturality
    ((HomologicalComplex.shortComplexFunctor A (ComplexShape.up ℕ) n).map f) G
  have : IsIso ((MixedCech.SheafExactness.MixedCechSheafExactness.mapHomologyIso G K n).hom ≫
      G.map (HomologicalComplex.homologyMap f n)) := by
    have h' : HomologicalComplex.homologyMap
        ((G.mapHomologicalComplex (ComplexShape.up ℕ)).map f) n ≫
          (MixedCech.SheafExactness.MixedCechSheafExactness.mapHomologyIso G L n).hom =
        (MixedCech.SheafExactness.MixedCechSheafExactness.mapHomologyIso G K n).hom ≫
          G.map (HomologicalComplex.homologyMap f n) := h
    exact h' ▸ inferInstance
  exact (isIso_comp_left_iff (MixedCech.SheafExactness.MixedCechSheafExactness.mapHomologyIso G K n).hom _).mp inferInstance

end General

include hU in
/-- Quasi-isomorphisms of sheaf complexes are detected after restriction to a cover. -/
theorem quasiIso_of_restrictions {K L : CochainComplex (Sheaves R X) ℕ} (f : K ⟶ L)
    (hf : ∀ i, QuasiIso (((MixedCech.CechRestriction.MixedCechRestriction.sheafRestrictionFunctor R (U i).ι).mapHomologicalComplex
      (ComplexShape.up ℕ)).map f)) : QuasiIso f := by
  constructor
  intro n
  apply (quasiIsoAt_iff_isIso_homologyMap f n).mpr
  apply isIso_of_restrictions R X U hU
  intro i
  have : QuasiIsoAt (((MixedCech.CechRestriction.MixedCechRestriction.sheafRestrictionFunctor R (U i).ι).mapHomologicalComplex
      (ComplexShape.up ℕ)).map f) n := (hf i).quasiIsoAt n
  exact map_homologyMap_isIso (MixedCech.CechRestriction.MixedCechRestriction.sheafRestrictionFunctor R (U i).ι) f n

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.Mixed.SheafQuasiIsoLocality.MixedSheafQuasiIsoLocality
