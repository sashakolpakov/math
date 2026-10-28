/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project
This file has been modified.
-/
import OAI.AlgebraicGeometry.SheafCohomology.Projective.TensorSections
import OAI.AlgebraicGeometry.SheafCohomology.Projective.Quasicoherent

/-! # Invertible Tensor Coherent -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.InvertibleTensorCoherent.Scheme.Modules

noncomputable section

open _root_.AlgebraicGeometry
open _root_.AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry.Scheme.Modules

/-!
# Quasicoherence after tensoring by an invertible sheaf

An invertible sheaf is trivial on an open cover. Refining that cover by affine
opens identifies the restriction of its tensor product with the restriction of
the other factor, so quasicoherence descends from the affine refinement.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits MonoidalCategory _root_.TopologicalSpace

universe u

variable {X : Scheme.{u}}

noncomputable local instance invertibleSheafTensorMonoidal
    (Y : Scheme.{u}) : MonoidalCategory Y.Modules :=
  Projective.Monoidal.Scheme.Modules.monoidalCategory Y

private noncomputable def tensorRestrictIso
    {M L : X.Modules} (U : X.Opens)
    (eL : L.restrict U.ι ≅ Invertible.Scheme.Modules.unitObj U.toScheme) :
    (M ⊗ L).restrict U.ι ≅ M.restrict U.ι := by
  letI : (Scheme.Modules.pullback U.ι).Monoidal :=
    PullbackTensorGeneral.Scheme.Modules.pullbackMonoidal U.ι
  exact
    (restrictFunctorIsoPullback U.ι).app (M ⊗ L) ≪≫
      (Functor.Monoidal.μIso
        (Scheme.Modules.pullback U.ι) M L).symm ≪≫
      ((restrictFunctorIsoPullback U.ι).symm.app M ⊗ᵢ
        (restrictFunctorIsoPullback U.ι).symm.app L) ≪≫
      (Iso.refl _ ⊗ᵢ eL) ≪≫
      (Iso.refl _ ⊗ᵢ
        (Invertible.Scheme.Modules.sheafifyValIso (Invertible.Scheme.Modules.unitObj U.toScheme)).symm) ≪≫
      ρ_ (M.restrict U.ι)

/-- Tensoring a quasicoherent scheme module by an invertible scheme module
preserves quasicoherence. -/
theorem _root_.OAI.AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.IsInvertible.tensorObj_isQuasicoherent
    {M L : X.Modules} [M.IsQuasicoherent]
    (hL : Invertible.Scheme.Modules.IsInvertible L) : (M ⊗ L).IsQuasicoherent := by
  let ML : X.Modules := M ⊗ L
  change ML.IsQuasicoherent
  obtain ⟨κ, V, hV, htriv⟩ := hL
  let J := {x : X.Opens × κ //
    x.1 ∈ X.affineOpens ∧ x.1 ≤ V x.2}
  let W : J → X.Opens := fun j => j.1.1
  have hW : IsOpenCover W :=
    X.isBasis_affineOpens.isOpenCover_mem_and_le
      (show IsOpenCover V from hV)
  have hlocal (j : J) :
      (ML.over (W j)).IsQuasicoherent := by
    let : IsAffine (W j).toScheme := j.2.1
    obtain ⟨eL⟩ := htriv j.1.2
    let eL' : L.restrict (W j).ι ≅ Invertible.Scheme.Modules.unitObj (W j).toScheme :=
      Invertible.Scheme.Modules.restrictIsoOfPullbackIso L (W j)
        (Invertible.Scheme.Modules.restrictTrivialization j.2.2 eL)
    let e :
        ML.restrict (W j).ι ≅ M.restrict (W j).ι :=
      tensorRestrictIso (M := M) (L := L) (W j) eL'
    have hRestrict :
        (ML.restrict (W j).ι).IsQuasicoherent :=
      (Quasicoherent.Scheme.Modules.isQuasicoherent (W j).toScheme).prop_of_iso
        e.symm inferInstance
    let : (ML.restrict (W j).ι).IsQuasicoherent :=
      hRestrict
    exact
      Quasicoherent.Scheme.Modules.isQuasicoherent_over_of_restrict_of_isAffineOpen
        ML (W j)
  have hcover :
      (Opens.grothendieckTopology X).CoversTop W := by
    rw [Opens.coversTop_iff]
    exact hW
  exact @SheafOfModules.IsQuasicoherent.of_coversTop
    _ _ _ _ _ _ _ _ ML _ W hcover hlocal

/-- Tensoring a finite-type quasicoherent scheme module by an invertible
scheme module preserves finite type. -/
theorem _root_.OAI.AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.IsInvertible.tensorObj_isFiniteType
    {M L : X.Modules} [M.IsQuasicoherent] [M.IsFiniteType]
    (hL : Invertible.Scheme.Modules.IsInvertible L) : (M ⊗ L).IsFiniteType := by
  let ML : X.Modules := M ⊗ L
  let : ML.IsQuasicoherent :=
    hL.tensorObj_isQuasicoherent
  obtain ⟨κ, V, hV, htriv⟩ := hL
  let J := {x : X.Opens × κ //
    x.1 ∈ X.affineOpens ∧ x.1 ≤ V x.2}
  let W : J → X.Opens := fun j => j.1.1
  have hW : IsOpenCover W :=
    X.isBasis_affineOpens.isOpenCover_mem_and_le
      (show IsOpenCover V from hV)
  choose G hG using fun j : J =>
    Quasicoherent.Scheme.Modules.exists_generatingSections_restrict_of_isFiniteType_of_isAffineOpen
      M ⟨W j, j.2.1⟩
  let e (j : J) : ML.restrict (W j).ι ≅ M.restrict (W j).ι := by
    let eL := Classical.choice (htriv j.1.2)
    let eL' : L.restrict (W j).ι ≅ Invertible.Scheme.Modules.unitObj (W j).toScheme :=
      Invertible.Scheme.Modules.restrictIsoOfPullbackIso L (W j)
        (Invertible.Scheme.Modules.restrictTrivialization j.2.2 eL)
    exact tensorRestrictIso (M := M) (L := L) (W j) eL'
  let GML (j : J) : (ML.restrict (W j).ι).GeneratingSections :=
    (SheafOfModules.GeneratingSections.equivOfIso (e j)).symm (G j)
  have hGML (j : J) : (GML j).IsFiniteType := by
    constructor
    change Finite (G j).I
    exact (hG j).finite
  have hcover :
      (Opens.grothendieckTopology X).CoversTop W := by
    rw [Opens.coversTop_iff]
    exact hW
  let q : ML.LocalGeneratorsData :=
    { I := J
      X := W
      coversTop := hcover
      generators := fun j =>
        Quasicoherent.Scheme.Modules.generatingSectionsOverOfRestrict ML (W j) (GML j) }
  have hq : q.IsFiniteType := by
    constructor
    intro j
    let : (GML j).IsFiniteType := hGML j
    exact Quasicoherent.Scheme.Modules.generatingSectionsOverOfRestrict_isFiniteType
      ML (W j) (GML j)
  have hqShrink : q.shrink.IsFiniteType := by
    constructor
    intro j
    dsimp [SheafOfModules.LocalGeneratorsData.shrink]
    exact hq.isFiniteType j.2.choose
  refine { exists_localGeneratorsData := ?_ }
  exact ⟨q.shrink, hqShrink⟩

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.InvertibleTensorCoherent.Scheme.Modules
