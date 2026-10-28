import OAI.NumberTheory.PadicHodge.IntegralComparison.Additive.OrderedCover
import OAI.NumberTheory.PadicHodge.IntegralComparison.OrderedCech.EdgeRefinement
import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.RelativeSupportedClass

/-! # Pure Section Class -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Global.PureSectionClass

noncomputable section

/-! A global section of the surviving cohomology sheaf gives the same
original total class on any affine cover, including actual refinements. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.HomologicalComplex
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X : Scheme.{u}} [X.IsSeparated]
  {ι κ : Type u} [LinearOrder ι] [LinearOrder κ]
  (U : ι → X.Opens) (haU : ∀ i, IsAffineOpen (U i))
  (K : CochainComplex X.Modules ℕ) [∀ q, (K.X q).IsQuasicoherent]
  (c : ℕ) (hK : ∀ q, q ≠ c → K.ExactAt q)

abbrev sheafCoefficients (M : X.Modules) (c : ℕ) :=
  RelativeCech.SupportedCoordinates.underlying AddCommGrpCat.{u} X
    (Principal.SingleAdditiveSections.sheafSingle M c)

def singleIso (M : X.Modules) (c q : ℕ) :=
  homologyMapIso (HomologicalComplex₂.total.mapIso
    (((OrderedCech.Functor.Projection.functor U).mapHomologicalComplex (.up ℕ)).mapIso
      (Principal.RelativeSupportedClass.singleCoefficientIso M c)) (.up ℕ)) q

def survivorIso (q : ℕ) := Additive.OrderedCechConcentration.iso U haU K c hK q ≪≫
  singleIso U (K.homology c) c q

abbrev edge (q : ℕ) := homologyMap
  (Presheaf.OrderedCechEdge.edge U (sheafCoefficients (K.homology c) c)) q

def map (q : ℕ) := edge U K c q ≫ (survivorIso U haU K c hK q).inv

variable (V : κ → X.Opens) (haV : ∀ i, IsAffineOpen (V i))
  (r : FormalCoproduct.mk κ V ⟶ FormalCoproduct.mk ι U)

omit [X.IsSeparated] in
private theorem coefficient_square (M : X.Modules) (c q : ℕ) :
    (singleIso U M c q).hom ≫
      homologyMap (OrderedCech.Refinement.totalMap U V r (sheafCoefficients M c)) q =
    Additive.OrderedCoverRefinement.homology U V r
      ((single X.Modules (.up ℕ) c).obj M) q ≫ (singleIso V M c q).hom := by
  let T := Functor.whiskerRight
    (NatTrans.mapHomologicalComplex (OrderedCech.Refinement.transformation U V r
      (D := AddCommGrpCat.{u})) (.up ℕ))
      (HomologicalComplex₂.totalFunctor AddCommGrpCat.{u} (.up ℕ) (.up ℕ) (.up ℕ))
  have h := congrArg (fun f => homologyMap f q)
    (T.naturality (Principal.RelativeSupportedClass.singleCoefficientIso M c).hom)
  simp only [homologyMap_comp] at h
  exact h

theorem survivor_refinement (q : ℕ) :
    (survivorIso U haU K c hK q).hom ≫
      homologyMap (OrderedCech.Refinement.totalMap U V r (sheafCoefficients (K.homology c) c)) q =
    Additive.OrderedCoverRefinement.homology U V r K q ≫
      (survivorIso V haV K c hK q).hom := by
  exact (DualComplexHomology.compose_squares _ _ _ _ _ _ _
    (Additive.OrderedCoverRefinement.concentration U V r haU haV K c hK q).symm
    (coefficient_square U V r (K.homology c) c q).symm).symm

theorem refinement (q : ℕ) : map U haU K c hK q ≫
    Additive.OrderedCoverRefinement.homology U V r K q = map V haV K c hK q := by
  apply (cancel_mono (survivorIso V haV K c hK q).hom).mp
  simp only [map, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [← survivor_refinement U haU K c hK V haV r q, Iso.inv_hom_id_assoc]
  exact OrderedCech.EdgeRefinement.homology U V r (sheafCoefficients (K.homology c) c) q

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Global.PureSectionClass
