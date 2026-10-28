import OAI.RepresentationTheory.Theta.Geometric.ParameterOpenCharts
import OAI.RepresentationTheory.Theta.Geometric.OpenFrameTransitionCoordinates

/-! # Line Iso Unit Descent -/

namespace OAI.RepresentationTheory.Theta.Geometric.LineIsoUnitDescent

noncomputable section

/-! Descended regular units reconstruct a global native line-bundle
isomorphism on the smaller parameter family. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {A R S : Type} [CommRing A] [CommRing R] [CommRing S]
    [Algebra A R] [Algebra A S] {Y : Scheme.{0}} (h : Y ⟶ Spec (.of A))

def parameterIsoOpenTopUnit {M N : Y.Modules}
    (a : (Scheme.Modules.pullback (ParameterOpenCharts.parameterProjection h R)).obj M ≅
      (Scheme.Modules.pullback (ParameterOpenCharts.parameterProjection h R)).obj N)
    (U : Y.Opens) (e : M.restrict U.ι ≅ AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj U.toScheme)
    (g : N.restrict U.ι ≅ AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj U.toScheme) :
    Γ((ParameterOpenCharts.parameterOpen h R U).toScheme, ⊤)ˣ :=
  OpenFrameTransitionCoordinates.moduleIsoOpenTopUnit a (ParameterOpenCharts.parameterOpen h R U)
    (Pullback.Algebraic.pullbackOpenFrame (ParameterOpenCharts.parameterProjection h R) M U e)
    (Pullback.Algebraic.pullbackOpenFrame (ParameterOpenCharts.parameterProjection h R) N U g)

theorem parameter_lineIso_of_unit_lifts [Flat h] (f : S →ₐ[A] R) (hf : Function.Injective f)
    {M N : Y.Modules} {ι : Type} (U : ι → Y.Opens) (hU : iSup U = ⊤)
    (e : ∀ i, M.restrict (U i).ι ≅ AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj (U i).toScheme)
    (g : ∀ i, N.restrict (U i).ι ≅ AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj (U i).toScheme)
    (a : (Scheme.Modules.pullback (ParameterOpenCharts.parameterProjection h R)).obj M ≅
      (Scheme.Modules.pullback (ParameterOpenCharts.parameterProjection h R)).obj N)
    (v : ∀ i, Γ((ParameterOpenCharts.parameterOpen h S (U i)).toScheme, ⊤)ˣ)
    (hv : ∀ i, Units.map (ParameterOpenCharts.parameterOpenMap h f (U i)).appTop.hom.toMonoidHom (v i) =
      parameterIsoOpenTopUnit h a (U i) (e i) (g i)) :
    Nonempty ((Scheme.Modules.pullback (ParameterOpenCharts.parameterProjection h S)).obj M ≅
      (Scheme.Modules.pullback (ParameterOpenCharts.parameterProjection h S)).obj N) := by
  let pS := ParameterOpenCharts.parameterProjection h S
  let eS (i) := Pullback.Algebraic.pullbackOpenFrame pS M (U i) (e i)
  let gS (i) := Pullback.Algebraic.pullbackOpenFrame pS N (U i) (g i)
  let cM (i j) := OpenFrameTransitionCoordinates.openFrameTransitionTopUnit M (U i) (U j) (e i) (e j)
  let cN (i j) := OpenFrameTransitionCoordinates.openFrameTransitionTopUnit N (U i) (U j) (g i) (g j)
  refine OpenTopUnitGluing.exists_iso_of_open_top_units (X := ParameterBaseChange.parameterBaseChange h S)
    ((Scheme.Modules.pullback pS).obj M) ((Scheme.Modules.pullback pS).obj N)
    (fun i => ParameterOpenCharts.parameterOpen h S (U i)) (pS.iSup_preimage_eq_top hU) eS gS v
    (fun i j => (pS ∣_ (U i ⊓ U j)).appTop (cM i j))
    (fun i j => (pS ∣_ (U i ⊓ U j)).appTop (cN i j)) ?_ ?_ ?_
  · intro i j
    exact OpenFrameTransitionCoordinates.pullbackOpenFrame_transition_scalar pS M (U i) (U j) (e i) (e j)
  · intro i j
    exact OpenFrameTransitionCoordinates.pullbackOpenFrame_transition_scalar pS N (U i) (U j) (g i) (g j)
  · intro i j
    exact ParameterOpenCharts.parameterOpen_transition_reflects h f hf (U i) (U j) (cM i j) (cN i j)
      (v i) (v j) (parameterIsoOpenTopUnit h a (U i) (e i) (g i))
      (parameterIsoOpenTopUnit h a (U j) (e j) (g j))
      (congrArg Units.val (hv i)) (congrArg Units.val (hv j))
      (OpenFrameTransitionCoordinates.moduleIsoOpenTopUnit_pullback_transition (ParameterOpenCharts.parameterProjection h R) a (U i) (U j)
        (e i) (e j) (g i) (g j))

end

end OAI.RepresentationTheory.Theta.Geometric.LineIsoUnitDescent
