import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Zariski.LocalFineIsoParameter
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FamilyLevelIsoRestriction
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SubterminalOpenChartRepresentation

/-! # Iso Open Chart -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polarized.IsoOpenChart

noncomputable section

/-! Every point of a locally Noetherian base has a constructed quasi-projective parameter chart whose natural map to the full polarized-isomorphism functor is a representable open immersion. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u

variable {S : Scheme.{u}} {g N : ℕ} {δ : Fin g → ℕ}

structure PolarizedIsoOpenChart (A B : PolarizationData.PolarizedAbelianWithFullLevel g δ N S) (x : S) where
  base : Scheme.{u}
  inclusion : base ⟶ S
  openImmersion : IsOpenImmersion inclusion
  covers : x ∈ Set.range inclusion
  parameter : Over base
  quasiProjective : Nonempty (Projective.ProjectivePresentations.QuasiProjectivePresentation parameter)
  mono : Mono parameter.hom
  representation : (Over.map inclusion).op ⋙ Family.LevelIsoFunctor.familyLevelIsoFunctor A B ≅ yoneda.obj parameter

def polarizedIsoOpenChart [IsLocallyNoetherian S]
    (A B : PolarizationData.PolarizedAbelianWithFullLevel g δ N S) (hδ : ∀ i, 0 < δ i) (hN : 3 ≤ N)
    (x : S) : PolarizedIsoOpenChart A B x := Classical.choice (by
  obtain ⟨Y, i, hi, hx, M, hM, hm, ⟨e⟩⟩ :=
    Zariski.LocalFineIsoParameter.polarizedIso_exists_local_quasiProjective_monomorphism A B hδ hN x
  exact ⟨⟨Y, i, hi, hx, M, hM, hm, (FamilyLevelIsoRestriction.rigidFamilyLevelIsoRestriction A B hN i).symm ≪≫ e⟩⟩)

namespace PolarizedIsoOpenChart

variable {A B : PolarizationData.PolarizedAbelianWithFullLevel g δ N S} {x : S} (C : PolarizedIsoOpenChart A B x)

def scheme : Over S := (Over.map C.inclusion).obj C.parameter

def toFunctor : yoneda.obj C.scheme ⟶ Family.LevelIsoFunctor.familyLevelIsoFunctor A B :=
  SubterminalOpenChartRepresentation.restrictedRepresentedChartMap (Family.LevelIsoFunctor.familyLevelIsoFunctor A B) C.inclusion C.parameter C.representation

theorem toFunctor_isOpenImmersion [IsLocallyNoetherian S] (hN : 3 ≤ N) :
    (Relative.RepresentableOpenGlueData.relativeOpenImmersions S).presheaf C.toFunctor := by
  have : IsOpenImmersion C.inclusion := C.openImmersion
  have : Mono C.parameter.hom := C.mono
  exact SubterminalOpenChartRepresentation.restrictedRepresentedChart_isOpenImmersion (Family.LevelIsoFunctor.familyLevelIsoFunctor A B)
    C.inclusion C.parameter C.representation
    (LocallyNoetherian.UniversalLevelRigidity.polarizedPullbackIsomorphisms_subsingleton_of_locallyNoetherian A B hN)

end PolarizedIsoOpenChart

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polarized.IsoOpenChart
