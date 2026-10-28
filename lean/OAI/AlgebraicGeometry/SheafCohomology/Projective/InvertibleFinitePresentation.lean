import OAI.AlgebraicGeometry.SheafCohomology.Projective.Invertible
import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
import Mathlib.CategoryTheory.Sites.Spaces

/-! # Invertible Finite Presentation -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.InvertibleFinitePresentation

noncomputable section

/-! Finite presentations from actual rank-one trivializations on an open cover. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace

universe u

section RankOne

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u}) [HasWeakSheafify J AddCommGrpCat.{u}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

def rankOneFreeIso (M : SheafOfModules.{u} R) (e : M ≅ SheafOfModules.unit R) :
    SheafOfModules.free (R := R) PUnit.{u + 1} ≅ M :=
  coproductUniqueIso (fun _ : PUnit.{u + 1} => SheafOfModules.unit R) ≪≫ e.symm

def rankOneGenerators (M : SheafOfModules.{u} R) (e : M ≅ SheafOfModules.unit R) :
    M.GeneratingSections :=
  (SheafOfModules.free.generatingSections PUnit.{u + 1}).ofEpi (rankOneFreeIso R M e).hom

instance rankOneGenerators_isIso (M : SheafOfModules.{u} R)
    (e : M ≅ SheafOfModules.unit R) : IsIso (rankOneGenerators R M e).π := by
  unfold rankOneGenerators
  rw [SheafOfModules.GeneratingSections.ofEpi_π,
    SheafOfModules.free.generatingSections_π]
  change IsIso (𝟙 (SheafOfModules.free (R := R) PUnit.{u + 1}) ≫ (rankOneFreeIso R M e).hom)
  rw [Category.id_comp]
  infer_instance

instance rankOneGenerators_finite (M : SheafOfModules.{u} R)
    (e : M ≅ SheafOfModules.unit R) : (rankOneGenerators R M e).IsFiniteType where
  finite := inferInstanceAs (Finite PUnit.{u + 1})

end RankOne

variable {X : Scheme.{u}} {M : X.Modules}

/-- A chosen cover and genuine rank-one frames over its opens. -/
structure RankOneCover (M : X.Modules) where
  I : Type u
  U : I → X.Opens
  covers : ⨆ i, U i = ⊤
  frame (i : I) : M.over (U i) ≅ SheafOfModules.unit (X.ringCatSheaf.over (U i))

def invertibleRankOneCover (hM : Invertible.Scheme.Modules.IsInvertible M) : RankOneCover M :=
  Classical.choice (by
    rcases hM with ⟨ι, U, hU, he⟩
    refine ⟨{ I := ι, U := U, covers := hU, frame := fun i => ?_ }⟩
    exact Invertible.Scheme.Modules.overTrivializationOfRestrictIso M (U i)
      (Invertible.Scheme.Modules.restrictIsoOfPullbackIso M (U i) (Classical.choice (he i))))

def rankOneCoverLocalGenerators (D : RankOneCover M) : M.LocalGeneratorsData where
  I := D.I
  X := D.U
  coversTop := (Opens.coversTop_iff (T := X) _).mpr D.covers
  generators i := rankOneGenerators _ _ (D.frame i)

instance rankOneCoverLocalGenerators_locallyFree (D : RankOneCover M) :
    (rankOneCoverLocalGenerators D).IsLocallyFreeData where
  isIso _ := rankOneGenerators_isIso _ _ _

/-- Finiteness of the original local presentation supplied by a rank-one cover. -/
abbrev rankOneCoverPresentationFinite (D : RankOneCover M) : Prop :=
  (rankOneCoverLocalGenerators D).quasiCoherentData.IsFinitePresentation

/-- The usual finite-presentation property of the original scheme module. -/
abbrev schemeModuleFinitePresentation (N : X.Modules) : Prop :=
  N.IsFinitePresentation

/-- The usual quasicoherence property of the original scheme module. -/
abbrev schemeModuleQuasicoherent (N : X.Modules) : Prop :=
  N.IsQuasicoherent

instance rankOneCoverPresentation_finite (D : RankOneCover M) :
    rankOneCoverPresentationFinite D where
  isFinite_presentation _ := {
    isFiniteType_generators := rankOneGenerators_finite _ _ _
    isFiniteType_relations := { finite := inferInstanceAs (Finite (ULift.{u} Empty)) } }

/-- Rank-one local frames give an actual finite presentation with one generator
and no relations on every cover member. -/
theorem invertible_finitePresentation (hM : Invertible.Scheme.Modules.IsInvertible M) :
    schemeModuleFinitePresentation M := by
  refine { exists_quasicoherentData := ?_ }
  exact ⟨(rankOneCoverLocalGenerators (invertibleRankOneCover hM)).quasiCoherentData,
    rankOneCoverPresentation_finite (invertibleRankOneCover hM)⟩

/-- The same explicit local presentation proves quasicoherence. -/
theorem invertible_quasicoherent (hM : Invertible.Scheme.Modules.IsInvertible M) :
    schemeModuleQuasicoherent M :=
  (rankOneCoverLocalGenerators (invertibleRankOneCover hM)).quasiCoherentData.isQuasicoherent

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.InvertibleFinitePresentation
