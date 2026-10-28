import OAI.NumberTheory.PadicHodge.IntegralComparison.Mapped.SingleGlobalSource
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.AdditiveGlobal
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.ModelAdditiveTop
import OAI.NumberTheory.PadicHodge.IntegralComparison.Ordered.SingleGlobalSourceCoefficients
import OAI.NumberTheory.PadicHodge.IntegralComparison.Open.CoverRefinementQuasiIso

/-! # Top Cover -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.TopCover

noncomputable section

/-! The actual native top-form map, globalized on any genuine cover
through the original single-sheaf coordinates and the flasque edge. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.HomologicalComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p]
  (n : ℕ) (X : Over (Spec (CommRingCat.of (Truncated.Witt.Ring p k n))))
  [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated]
  (Y : Over (Spec (CommRingCat.of k))) [IsSeparated Y.hom] (f : Y.left ⟶ X.left)
  (hp : IsPullback f Y.hom X.hom
    (Spec.map (CommRingCat.ofHom (Truncated.Witt.reduction p k n))))
  (I : InjectiveResolution (BoundedCrystalline.CrystallineCohomology.structureSheaf (p := p)
    (J := Ideal.span {(p : WittVector p k)}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k)
    (Witt.Crystalline.wittStructureMap p k Y) n))
  (g : ℕ) [SmoothOfRelativeDimension g X.hom]

abbrev coefficients : X.left.Modules ⥤ X.left.Opensᵒᵖ ⥤ AddCommGrpCat.{2} :=
  Relative.AdditiveCechConcentration.presheaves (X := X.left) ⋙
    (Functor.whiskeringRight X.left.Opensᵒᵖ AddCommGrpCat.{0} AddCommGrpCat.{2}).obj
      AdditiveTop.Comparison.lift
abbrev form := GeometricComparison.Integral.FormsModules.IntegralFormsModules.sheaf (Truncated.Witt.Ring p k n) X g
abbrev target := AdditiveTop.Comparison.target p k n X Y f I

def sourceMap : ((coefficients p k n X).mapHomologicalComplex (.up ℕ)).obj
    ((single X.left.Modules (.up ℕ) g).obj (form p k n X g)) ⟶ target p k n X Y f I :=
  AdditiveTop.Comparison.map p k n X Y f hp I g

variable {ι κ ν : Type} [LinearOrder ι] [LinearOrder κ] [LinearOrder ν]
  (U : ι → X.left.Opens) (hU : iSup U = ⊤)

abbrev originalIso := IntegralComparison.Functor.SingleTotal.homologyIso
  (coefficients p k n X ⋙ OrderedCech.Functor.Projection.functor U) (form p k n X g) g g

def globalMap :
    (OrderedCech.Projection.complex U ((coefficients p k n X).obj (form p k n X g))).homology g ⟶
      (Presheaf.OrderedCechEdge.sections (target p k n X Y f I)).homology (g+g) := by
  letI := AdditiveGlobal.ResolutionFlasque.additive_edge_isIso p k n X Y f I U hU (g+g)
  exact Mapped.SingleGlobalSource.map (coefficients p k n X) (form p k n X g) g
    (target p k n X Y f I) (sourceMap p k n X Y f hp I g) U

theorem original_coordinates :
    letI := AdditiveGlobal.ResolutionFlasque.additive_edge_isIso p k n X Y f I U hU (g+g)
    (originalIso p k n X g U).hom ≫ globalMap p k n X Y f hp I g U hU =
      homologyMap ((OrderedCech.TotalProjection.ordered U).map
        (sourceMap p k n X Y f hp I g)) (g+g) ≫
      inv (homologyMap (Presheaf.OrderedCechEdge.edge U (target p k n X Y f I)) (g+g)) := by
  let := AdditiveGlobal.ResolutionFlasque.additive_edge_isIso p k n X Y f I U hU (g+g)
  exact Mapped.SingleGlobalSource.coordinates_map (coefficients p k n X) (form p k n X g) g
    (target p k n X Y f I) (sourceMap p k n X Y f hp I g) U

variable (V : κ → X.left.Opens) (hV : iSup V = ⊤) (haV : ∀ j, IsAffineOpen (V j))
  (T : ν → X.left.Opens) (hT : iSup T = ⊤) (haT : ∀ j, IsAffineOpen (T j))
  (rU : FormalCoproduct.mk ν T ⟶ FormalCoproduct.mk ι U)
  (rV : FormalCoproduct.mk ν T ⟶ FormalCoproduct.mk κ V)

include hV hT haV haT in
omit [Fintype k] [CharP k p] [SmoothOfRelativeDimension g X.hom] in
theorem source_refinement_isIso :
    IsIso (homologyMap (OrderedCech.Refinement.map V T rV
      ((coefficients p k n X).obj (form p k n X g))) g) := by
  let : (form p k n X g).IsQuasicoherent :=
    IntegralComparison.Smooth.FormCoherence.Integral.quasicoherent (Truncated.Witt.Ring p k n) X g
  let : QuasiIso (GeometricComparison.NonemptyCech.Refinement.NonemptyCechRefinement.map V T rV (form p k n X g).presheaf) :=
    Open.CoverRefinementQuasiIso.Cech.quasiIso V T rV (form p k n X g) ⊤ hV hT haV haT
  let := OrderedCech.Refinement.quasiIso V T rV (form p k n X g).presheaf
  exact Ordered.SingleGlobalSourceCoefficients.refinement_isIso
    AdditiveTop.Comparison.lift (form p k n X g).presheaf V T rV g

include hV hT haV haT in
def coefficientComparison := by
  letI := source_refinement_isIso p k n X g V hV haV T hT haT rV
  exact Ordered.SingleGlobalSource.coefficientComparison
    ((coefficients p k n X).obj (form p k n X g)) g U V T rU rV

theorem common_refinement :
    globalMap p k n X Y f hp I g U hU =
      coefficientComparison p k n X g U V hV haV T hT haT rU rV ≫
        globalMap p k n X Y f hp I g V hV := by
  let := AdditiveGlobal.ResolutionFlasque.additive_edge_isIso p k n X Y f I U hU (g+g)
  let := AdditiveGlobal.ResolutionFlasque.additive_edge_isIso p k n X Y f I V hV (g+g)
  let := AdditiveGlobal.ResolutionFlasque.additive_edge_isIso p k n X Y f I T hT (g+g)
  let := source_refinement_isIso p k n X g V hV haV T hT haT rV
  exact Mapped.SingleGlobalSource.common_refinement
    (coefficients p k n X) (form p k n X g) g (target p k n X Y f I)
    (sourceMap p k n X Y f hp I g) U V T rU rV

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.TopCover
