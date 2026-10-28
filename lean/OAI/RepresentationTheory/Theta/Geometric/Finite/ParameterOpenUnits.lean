import OAI.RepresentationTheory.Theta.Geometric.ParameterOpenCharts
import OAI.RepresentationTheory.Theta.Geometric.Finite.AffineChartUnits

/-! # Parameter Open Units -/

namespace OAI.RepresentationTheory.Theta.Geometric.Finite.ParameterOpenUnits

noncomputable section

/-! Regular units on finitely many actual affine opens of a flat
base-changed family descend to a common finite-type parameter algebra. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem exists_fg_parameterOpen_units
    {A R ι : Type} [CommRing A] [CommRing R] [Algebra A R] [Fintype ι]
    {Y : Scheme} (h : Y ⟶ Spec (.of A)) [Flat h]
    (U : ι → Y.Opens) (hU : ∀ i, IsAffineOpen (U i))
    (u : ∀ i, Γ((ParameterOpenCharts.parameterOpen h R (U i)).toScheme, ⊤)ˣ) :
    ∃ S : Subalgebra A R, S.FG ∧ ∃ v : ∀ i, Γ((ParameterOpenCharts.parameterOpen h S (U i)).toScheme, ⊤)ˣ,
      ∀ i, Units.map (ParameterOpenCharts.parameterOpenMap h S.val (U i)).appTop.hom.toMonoidHom (v i) = u i := by
  let : ∀ i, IsAffine (U i).toScheme := hU
  let : ∀ i, Algebra A Γ((U i).toScheme, ⊤) := fun i => Affine.StructureCoordinates.affineStructureAlgebra ((U i).ι ≫ h)
  let : ∀ i, Module.Flat A Γ((U i).toScheme, ⊤) := fun i => Affine.StructureCoordinates.affineStructure_flat ((U i).ι ≫ h)
  exact AffineChartUnits.exists_fg_subalgebra_finite_affine_chart_units (fun i => Γ((U i).toScheme, ⊤))
    (fun i => (ParameterOpenCharts.parameterOpen h R (U i)).toScheme) (fun S i => (ParameterOpenCharts.parameterOpen h S (U i)).toScheme)
    (fun i => ParameterOpenCharts.parameterOpenCoordinateIso h R (U i) (hU i))
    (fun S i => ParameterOpenCharts.parameterOpenCoordinateIso h S (U i) (hU i))
    (fun S i => ParameterOpenCharts.parameterOpenMap h S.val (U i))
    (fun S i => ParameterOpenCharts.parameterOpenCoordinateIso_natural h S.val (U i) (hU i)) u

end

end OAI.RepresentationTheory.Theta.Geometric.Finite.ParameterOpenUnits
