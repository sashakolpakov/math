import OAI.NumberTheory.PadicHodge.IntegralComparison.OrderedCech.QuasiIso
import OAI.NumberTheory.PadicHodge.IntegralComparison.BicomplexHorizontalEdge

/-! # Total Naturality -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.OrderedCech.TotalNaturality

noncomputable section

/-! The native augmentation from global sections to the ordered Čech
total commutes with every map of sheaf complexes. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false

universe u

variable {X S : Scheme.{u}} (π : X ⟶ S)
  {ι : Type u} [LinearOrder ι] (U : ι → X.Opens)
  {K L : CochainComplex X.Modules ℕ} (a : K ⟶ L)

def sectionMap : Total.Comparison.sectionComplex π K ⟶
    Total.Comparison.sectionComplex π L :=
  ((Augmentation.sections π).mapHomologicalComplex (.up ℕ)).map a

@[reassoc]
theorem edge_naturality (hU : iSup U = ⊤) :
    Total.Comparison.edge π U K hU ≫ QuasiIso.map π U a =
      sectionMap π a ≫ Total.Comparison.edge π U L hU :=
  BicomplexHorizontalEdge.naturality _ _ _ _ _ _ _ _ _ _
    (QuasiIso.bicomplexMap π U a) (sectionMap π a)
    (fun q => (Augmentation.naturality π U (a.f q)).symm)

@[reassoc]
theorem homology_naturality (hU : iSup U = ⊤)
    (hK : ∀ q p, IsZero ((AlgebraicGeometry.SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.orderedBaseCechComplex π (K.X q) U).homology (p + 1)))
    (hL : ∀ q p, IsZero ((AlgebraicGeometry.SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.orderedBaseCechComplex π (L.X q) U).homology (p + 1)))
    (n : ℕ) :
    (Total.Comparison.homologyIso π U K hU hK n).hom ≫
        HomologicalComplex.homologyMap (QuasiIso.map π U a) n =
      HomologicalComplex.homologyMap (sectionMap π a) n ≫
        (Total.Comparison.homologyIso π U L hU hL n).hom := by
  have h := congrArg (fun f => HomologicalComplex.homologyMap f n) (edge_naturality π U a hU)
  simpa only [Total.Comparison.homologyIso, isoOfQuasiIsoAt_hom,
    HomologicalComplex.homologyMap_comp] using h

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.OrderedCech.TotalNaturality
