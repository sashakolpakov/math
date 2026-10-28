import OAI.RepresentationTheory.Theta.Adelic.CompactDefinitePlace
import OAI.RepresentationTheory.Theta.Adelic.BallGroupComparison
import OAI.RepresentationTheory.Theta.Adelic.GeometricGroup
import Mathlib.Topology.Homeomorph.Lemmas

/-! # Geometric Ball Projection -/

namespace OAI.RepresentationTheory.Theta.Adelic.GeometricBallProjection

noncomputable section

/-! Projection to the distinguished ball group is surjective and closed:
the omitted native special-unitary factors are compact. -/

open scoped Classical _root_.NumberField

open _root_.Matrix OAI.RepresentationTheory.Theta.Adelic.SpecialUnitary OAI.RepresentationTheory.Theta.Adelic.RationalSU
open OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.BallNatural OAI.RepresentationTheory.Theta.Adelic.CompactDefinitePlace
open OAI.RepresentationTheory.Theta.Adelic.BallGroupComparison OAI.RepresentationTheory.Theta.Adelic.GeometricGroup

variable {F : Type} [Field F] [NumberField F] {d : F} {m : ℕ}
variable {H : (Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {K : (Matrix (Fin m) (Fin m) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable (A : BallGeometryData.BallArithmeticData F d m H K)

def distinguishedNativeEquiv :
    SpecialUnitary.SU (Weil.AdelicSplitting.Integral.Construction.localizedForm F H.val (.inl (A.enumerate A.distinguished))) ≃ₜ* BallNatural.BallGroup :=
  (CompactDefinitePlace.nativeNormalizedUnitary A A.distinguished).trans
    (BallGroupComparison.specialUnitaryFormCongr _ _ (GeometricGroup.distinguished_standard_form A))

theorem geometricBallHom_eq (g : RationalSU.ArchimedeanSU F H) :
    GeometricGroup.geometricBallHom A g = distinguishedNativeEquiv A (g (A.enumerate A.distinguished)) := by
  apply Subtype.ext
  rfl

theorem geometricBallHom_surjective : Function.Surjective (GeometricGroup.geometricBallHom A) := by
  intro g
  let e := Homeomorph.piSplitAt (A.enumerate A.distinguished)
    (fun v => SpecialUnitary.SU (Weil.AdelicSplitting.Integral.Construction.localizedForm F H.val (.inl v)))
  refine ⟨e.symm ((distinguishedNativeEquiv A).symm g, 1), ?_⟩
  rw [geometricBallHom_eq]
  have he := congrArg Prod.fst (e.apply_symm_apply ((distinguishedNativeEquiv A).symm g, 1))
  exact (congrArg (distinguishedNativeEquiv A) he).trans
    ((distinguishedNativeEquiv A).apply_symm_apply g)

theorem geometricBallHom_closed : IsClosedMap (GeometricGroup.geometricBallHom A) := by
  let : ∀ v : {v : NumberField.InfinitePlace F // v ≠ A.enumerate A.distinguished},
      CompactSpace (SpecialUnitary.SU (Weil.AdelicSplitting.Integral.Construction.localizedForm F H.val (.inl v.val))) := by
    intro v
    obtain ⟨w, hw⟩ := A.enumerate.surjective v.val
    have hn : w ≠ A.distinguished := by
      intro h
      exact v.property (hw.symm.trans (congrArg A.enumerate h))
    exact hw ▸ CompactDefinitePlace.native_definite_compact A w hn
  let e := Homeomorph.piSplitAt (A.enumerate A.distinguished)
    (fun v => SpecialUnitary.SU (Weil.AdelicSplitting.Integral.Construction.localizedForm F H.val (.inl v)))
  have he : (GeometricGroup.geometricBallHom A : RationalSU.ArchimedeanSU F H → BallNatural.BallGroup) =
      distinguishedNativeEquiv A ∘ Prod.fst ∘ e := by
    funext g
    exact geometricBallHom_eq A g
  rw [he]
  exact (distinguishedNativeEquiv A).toHomeomorph.isClosedMap.comp
    (isClosedMap_fst_of_compactSpace.comp e.isClosedMap)

end

end OAI.RepresentationTheory.Theta.Adelic.GeometricBallProjection
