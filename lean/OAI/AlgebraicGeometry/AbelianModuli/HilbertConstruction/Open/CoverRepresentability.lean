import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.GeneralRestrictedRepresentedCharts
import Mathlib.CategoryTheory.ShrinkYoneda
import Mathlib.CategoryTheory.Sites.SheafOfTypes
import Mathlib.AlgebraicGeometry.Morphisms.Basic

/-! # Cover Representability -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Open.CoverRepresentability

noncomputable section

/-! Representability is local on the base for a Zariski sheaf of sets.
The values of the sheaf may lie in a larger universe: their smallness is
proved from separatedness and the supplied local representing schemes.
The output has native pullback comparisons with those original schemes. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u v

def restrictSchemeRepresentable {S U : Scheme.{u}}
    {F : (Over S)ᵒᵖ ⥤ Type v} {X : Over S}
    (r : F.RepresentableBy X) (i : U ⟶ S) :
    ((Over.map i).op ⋙ F).RepresentableBy ((Over.pullback i).obj X) where
  homEquiv {T} := ((Over.mapPullbackAdj i).homEquiv T X).symm.trans r.homEquiv
  homEquiv_comp {T V} a b := by
    have h : ((Over.mapPullbackAdj i).homEquiv T X).symm (a ≫ b) =
        (Over.map i).map a ≫ ((Over.mapPullbackAdj i).homEquiv V X).symm b := by
      apply Over.OverMorphism.ext
      exact Category.assoc _ _ _
    exact (congrArg r.homEquiv h).trans
      (r.homEquiv_comp ((Over.map i).map a)
        (((Over.mapPullbackAdj i).homEquiv V X).symm b))

namespace OpenCoverRepresentability

variable {S : Scheme.{u}} (F : (Over S)ᵒᵖ ⥤ Type v) (U : S.OpenCover.{u})
  (M : ∀ j, Over (U.X j))
  (r : ∀ j, ((Over.map (U.f j)).op ⋙ F).RepresentableBy (M j))
  (hF : Presieve.IsSheaf (Scheme.zariskiTopology.over S) F)

def restrictionCode (T : Over S) (s : F.obj (.op T)) :
    ∀ j, (Over.pullback (U.f j)).obj T ⟶ M j :=
  fun j => (r j).homEquiv.symm (F.map (SubterminalRelativeChart.baseChartProjection (U.f j) T).op s)

include hF in
theorem restrictionCode_injective (T : Over S) :
    Function.Injective (restrictionCode F U M r T) := by
  intro s t hst
  have hcover :
      Sieve.ofArrows (fun j => SubterminalRelativeChart.baseChartTest (U.f j) T)
        (fun j => SubterminalRelativeChart.baseChartProjection (U.f j) T) ∈ (Scheme.zariskiTopology.over S) T := by
    rw [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_ofArrows]
    exact Scheme.Cover.mem_grothendieckTopology (U.pullback₁ T.hom)
  apply (hF _ hcover).isSeparatedFor.ext
  intro V f hf
  obtain ⟨j, a, ha⟩ := (Sieve.mem_ofArrows_iff _ _ _).mp hf
  have hj : F.map (SubterminalRelativeChart.baseChartProjection (U.f j) T).op s =
      F.map (SubterminalRelativeChart.baseChartProjection (U.f j) T).op t :=
    (r j).homEquiv.symm.injective (congrFun hst j)
  rw [ha, op_comp, F.map_comp_apply, F.map_comp_apply, hj]

include U M r hF in
theorem smallValues : FunctorToTypes.Small.{u} F :=
  fun T => small_of_injective (restrictionCode_injective F U M r hF T.unop)

def smallPresheaf : (Over S)ᵒᵖ ⥤ Type u := by
  let : FunctorToTypes.Small.{u} F := smallValues F U M r hF
  exact FunctorToTypes.shrink.{u} F

def chartRepresentable (j : U.I₀) :
    ((Over.map (U.f j)).op ⋙ smallPresheaf F U M r hF).RepresentableBy (M j) := by
  let : FunctorToTypes.Small.{u} F := smallValues F U M r hF
  refine
    { homEquiv := (r j).homEquiv.trans (equivShrink.{u} _)
      homEquiv_comp := ?_ }
  intro T V a b
  change equivShrink.{u} _ ((r j).homEquiv (a ≫ b)) =
    equivShrink.{u} _ (F.map ((Over.map (U.f j)).map a).op
      ((equivShrink.{u} _).symm (equivShrink.{u} _ ((r j).homEquiv b))))
  rw [Equiv.symm_apply_apply]
  exact congrArg (equivShrink.{u} _) ((r j).homEquiv_comp a b)

def chartIso (j : U.I₀) :
    (Over.map (U.f j)).op ⋙ smallPresheaf F U M r hF ≅ yoneda.obj (M j) :=
  (chartRepresentable F U M r hF j).toIso.symm

theorem smallPresheaf_isSheaf :
    Presheaf.IsSheaf (Scheme.zariskiTopology.over S) (smallPresheaf F U M r hF) := by
  let : FunctorToTypes.Small.{u} F := smallValues F U M r hF
  apply (isSheaf_iff_isSheaf_of_type _ _).mpr
  apply Presieve.isSheaf_of_nat_equiv
    (fun {T} => equivShrink.{u} (F.obj (.op T))) _ hF
  intro T V a s
  change equivShrink.{u} _ (F.map a.op s) =
    equivShrink.{u} _ (F.map a.op ((equivShrink.{u} _).symm (equivShrink.{u} _ s)))
  rw [Equiv.symm_apply_apply]

theorem chart_open (j : U.I₀) :
    (Relative.RepresentableOpenGlueData.relativeOpenImmersions S).presheaf
      (SubterminalOpenChartRepresentation.restrictedRepresentedChartMap (smallPresheaf F U M r hF) (U.f j) (M j)
        (chartIso F U M r hF j)) :=
  GeneralRestrictedRepresentedCharts.generalRestrictedRepresentedChart_isOpenImmersion _ _ _ _

local instance chart_cover :
    Presheaf.IsLocallySurjective (Scheme.zariskiTopology.over S)
      (Sigma.desc (fun j => SubterminalOpenChartRepresentation.restrictedRepresentedChartMap
        (smallPresheaf F U M r hF) (U.f j) (M j) (chartIso F U M r hF j))) :=
  GeneralRestrictedRepresentedCharts.generalRestrictedRepresentedCharts_locallySurjective _ _ _ _

def scheme : Over S := Relative.LocalRepresentationSection.relativeLocalRepresentationScheme (chart_open F U M r hF)

def smallRepresentable :
    (smallPresheaf F U M r hF).RepresentableBy (scheme F U M r hF) :=
  Functor.representableByEquiv.symm
    (Relative.LocalRepresentability.relativeLocalRepresentationIso (chart_open F U M r hF)
      (smallPresheaf_isSheaf F U M r hF)).symm

def representable : F.RepresentableBy (scheme F U M r hF) := by
  let : FunctorToTypes.Small.{u} F := smallValues F U M r hF
  refine
    { homEquiv := (smallRepresentable F U M r hF).homEquiv.trans (equivShrink.{u} _).symm
      homEquiv_comp := ?_ }
  intro T V a b
  change (equivShrink.{u} _).symm ((smallRepresentable F U M r hF).homEquiv (a ≫ b)) = _
  rw [(smallRepresentable F U M r hF).homEquiv_comp]
  change (equivShrink.{u} _).symm
    (equivShrink.{u} _ (F.map a.op
      ((equivShrink.{u} _).symm ((smallRepresentable F U M r hF).homEquiv b)))) = _
  exact (equivShrink.{u} _).symm_apply_apply _

def chartPullbackIso (j : U.I₀) :
    M j ≅ (Over.pullback (U.f j)).obj (scheme F U M r hF) :=
  (r j).uniqueUpToIso (restrictSchemeRepresentable (representable F U M r hF) (U.f j))

theorem chartPullbackIso_class (j : U.I₀) :
    (restrictSchemeRepresentable (representable F U M r hF) (U.f j)).homEquiv
        (chartPullbackIso F U M r hF j).hom =
      (r j).homEquiv (𝟙 (M j)) := by
  exact (restrictSchemeRepresentable (representable F U M r hF) (U.f j)).homEquiv.apply_symm_apply _

theorem localProperty (Q : MorphismProperty Scheme.{u}) [IsZariskiLocalAtTarget Q]
    (hQ : ∀ j, Q (M j).hom) : Q (scheme F U M r hF).hom := by
  apply IsZariskiLocalAtTarget.of_openCover U
  intro j
  let e := chartPullbackIso F U M r hF j
  let a : Arrow.mk (M j).hom ≅
      Arrow.mk (U.pullbackHom (scheme F U M r hF).hom j) :=
    Arrow.isoMk ((Over.forget (U.X j)).mapIso e) (Iso.refl _) (by
      change e.hom.left ≫ pullback.snd (scheme F U M r hF).hom (U.f j) =
        (M j).hom ≫ 𝟙 (U.X j)
      exact e.hom.w.trans (Category.comp_id (M j).hom).symm)
  exact (Q.arrow_mk_iso_iff a).mp (hQ j)

end OpenCoverRepresentability

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Open.CoverRepresentability
