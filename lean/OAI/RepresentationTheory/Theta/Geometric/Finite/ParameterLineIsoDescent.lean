import OAI.RepresentationTheory.Theta.Geometric.LineIsoUnitDescent
import OAI.RepresentationTheory.Theta.Geometric.Finite.ParameterOpenUnits
import OAI.RepresentationTheory.Theta.Geometric.Finite.CommonFrames

/-! # Parameter Line Iso Descent -/

namespace OAI.RepresentationTheory.Theta.Geometric.Finite.ParameterLineIsoDescent

noncomputable section

/-! An actual isomorphism of two line bundles on a quasi-compact
flat family is already defined over a finitely generated subalgebra
of its arbitrary parameter algebra. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem exists_fg_parameter_lineIso_of_finite_frames
    {A R ι : Type} [CommRing A] [CommRing R] [Algebra A R] [Fintype ι]
    {Y : Scheme.{0}} (h : Y ⟶ Spec (.of A)) [Flat h]
    {M N : Y.Modules} (U : ι → Y.Opens) (hU : ∀ i, IsAffineOpen (U i)) (hcover : iSup U = ⊤)
    (e : ∀ i, M.restrict (U i).ι ≅ AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj (U i).toScheme)
    (g : ∀ i, N.restrict (U i).ι ≅ AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj (U i).toScheme)
    (a : (Scheme.Modules.pullback (ParameterOpenCharts.parameterProjection h R)).obj M ≅
      (Scheme.Modules.pullback (ParameterOpenCharts.parameterProjection h R)).obj N) :
    ∃ S : Subalgebra A R, S.FG ∧
      Nonempty ((Scheme.Modules.pullback (ParameterOpenCharts.parameterProjection h S)).obj M ≅
        (Scheme.Modules.pullback (ParameterOpenCharts.parameterProjection h S)).obj N) := by
  obtain ⟨S, hS, v, hv⟩ := ParameterOpenUnits.exists_fg_parameterOpen_units h U hU
    (fun i => LineIsoUnitDescent.parameterIsoOpenTopUnit h a (U i) (e i) (g i))
  exact ⟨S, hS, LineIsoUnitDescent.parameter_lineIso_of_unit_lifts h S.val Subtype.val_injective U hcover e g a v hv⟩

theorem exists_fg_parameter_lineIso
    {A R : Type} [CommRing A] [CommRing R] [Algebra A R]
    {Y : Scheme.{0}} [CompactSpace Y] (h : Y ⟶ Spec (.of A)) [Flat h]
    (L N : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle Y)
    (a : (L.pullback (ParameterOpenCharts.parameterProjection h R)).sheaf ≅ (N.pullback (ParameterOpenCharts.parameterProjection h R)).sheaf) :
    ∃ S : Subalgebra A R, S.FG ∧
      Nonempty ((L.pullback (ParameterOpenCharts.parameterProjection h S)).sheaf ≅ (N.pullback (ParameterOpenCharts.parameterProjection h S)).sheaf) := by
  classical
  obtain ⟨k, U, hU, he, hg, hcover⟩ := CommonFrames.exists_finite_common_affine_frames L N
  let e i := Classical.choice (he i)
  let g i := Classical.choice (hg i)
  exact exists_fg_parameter_lineIso_of_finite_frames h U hU hcover
    (fun i => (Scheme.Modules.restrictFunctorIsoPullback (U i).ι).app L.sheaf ≪≫ e i)
    (fun i => (Scheme.Modules.restrictFunctorIsoPullback (U i).ι).app N.sheaf ≪≫ g i) a

end

end OAI.RepresentationTheory.Theta.Geometric.Finite.ParameterLineIsoDescent
