import OAI.AlgebraicGeometry.Comparison.Betti.BrutalCechColumns
import OAI.AlgebraicGeometry.Comparison.Betti.BrutalCechAcyclicity
import OAI.AlgebraicGeometry.Comparison.Betti.Cech.ConcreteDerived

/-! # Brutal Concrete Derived -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.BrutalConcreteDerived.Hodge

noncomputable section

/-! Every independent Hodge truncation has the actual derived coefficient comparison on a proved finite acyclic Čech cover. -/

open _root_.CategoryTheory _root_.TopologicalSpace

open OAI.AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration OAI.AlgebraicGeometry.Comparison.Betti.Cech.ConcreteDerived.Godement

variable {X Y : TopCat.{0}} (f : Y ⟶ X) {ι : Type} [Finite ι] (U : ι → Opens X)
  (K : CochainComplex (ConstantSheafSections.ComplexSheaves X) ℕ)
  (L : CochainComplex (ConstantSheafSections.ComplexSheaves Y) ℕ)
  (α : K ⟶ ((TopologicalSheafPullback.sheafDirectImage f).mapHomologicalComplex (.up ℕ)).obj L) (r : ℤ)

theorem brutal_directImageCohomologyMap_bijective
    (hU : iSup U = ⊤) (hV : (⨆ i, (Opens.map f).obj (U i)) = ⊤)
    (hK : ∀ q, SheafCohomology.Cech.VerticalComparison.TopCat.Sheaf.CechIntersectionsAcyclic (X := X) U
      ((Complex.SheafForget.Flasque.sheafForget X).obj (K.X q)))
    (hL : ∀ q, SheafCohomology.Cech.VerticalComparison.TopCat.Sheaf.CechIntersectionsAcyclic (X := Y) (fun i => (Opens.map f).obj (U i))
      ((Complex.SheafForget.Flasque.sheafForget Y).obj (L.X q)))
    (hα : ∀ q, QuasiIso ((Sheaf.CechPullbackTotal.sheafCechPullbackBicomplexMap f U (Godement.AdditiveImage.additiveDirectImageComplexMap f α)).f q))
    (n : ℤ) :
    Function.Bijective (FlasqueDerived.directImageCohomologyMap f ((Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.brutal K r).extend (ComplexShape.embeddingUpIntGE 0))
      ((Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.brutal L r).extend (ComplexShape.embeddingUpIntGE 0))
      (ImageExtensionSquare.extendDirectImageComplexMap f (BrutalCechAcyclicity.Hodge.brutalSheafDirectImageMap f α r)) n) :=
  Cech.ConcreteDerived.Godement.cech_directImageCohomologyMap_bijective f U (Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.brutal K r) (Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.brutal L r) (BrutalCechAcyclicity.Hodge.brutalSheafDirectImageMap f α r)
    hU hV (BrutalCechAcyclicity.Hodge.brutalCechIntersectionsAcyclic U K r hK)
    (BrutalCechAcyclicity.Hodge.brutalCechIntersectionsAcyclic (fun i => (Opens.map f).obj (U i)) L r hL)
    (BrutalCechColumns.Hodge.brutalCechPullbackTotal_quasiIso f U α r hα) n

end

end OAI.AlgebraicGeometry.Comparison.Betti.BrutalConcreteDerived.Hodge
