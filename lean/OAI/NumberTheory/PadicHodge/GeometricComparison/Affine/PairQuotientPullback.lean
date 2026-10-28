import OAI.NumberTheory.PadicHodge.GeometricComparison.IndexedOrdinaryCech
import OAI.NumberTheory.PadicHodge.GeometricComparison.Affine.PairOrdinaryPullback

/-! # Pair Quotient Pullback -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Affine.PairQuotientPullback.AffinePairQuotientPullback

noncomputable section

/-! Ordinary coefficient-quotient coordinates preserve the actual
geometric pullback of forms on compatible affine pairs. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

variable (R : Type) [CommRing R]
  {X Y : Over (Spec (CommRingCat.of R))} (f : X ⟶ Y) (I : Ideal R)

local notation "Q" => OAI.NumberTheory.PadicHodge.IntegralComparison.Module.IdealQuotient.functor R I
local notation "S" => OAI.NumberTheory.PadicHodge.GeometricComparison.Affine.PairOrdinaryForms.AffinePairOrdinaryForms.sourceOpens R f
local notation "T" => OAI.NumberTheory.PadicHodge.GeometricComparison.Affine.PairOrdinaryForms.AffinePairOrdinaryForms.targetOpens R f

def transformation := Functor.whiskerRight (PairSectionAlgebraPullback.AffinePairSectionAlgebraPullback.transformation R f)
  (IntegralComparison.OrdinaryDeRhamFunctor.Ordinary.functor R ⋙ (Q).mapHomologicalComplex (.up ℕ))

def coordinateMap := (IndexedOrdinaryCech.IndexedOrdinaryQuotientCech.complexIso R Y T I).inv ≫
  AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly.map (.up ℕ) (transformation R f I) ≫ (IndexedOrdinaryCech.IndexedOrdinaryQuotientCech.complexIso R X S I).hom

def originalMap : OrdinaryAffineTotal.OrdinaryAffineQuotientCech.quotientComplex R Y I ⟶
    ((Cech.Image.CechImage.functor R f.left).mapHomologicalComplex (.up ℕ)).obj
      (OrdinaryAffineTotal.OrdinaryAffineQuotientCech.quotientComplex R X I) :=
  ((IntegralCech.QuotientTotal.IntegralCechQuotientTotal.presheaves R Y I).mapHomologicalComplex (.up ℕ)).map (DeRham.Int.presheafPullback f)

theorem component (q : ℕ) (U : (MapPairs.AffineMapPairs.Charts f.left)ᵒᵖ) :
    ((coordinateMap R f I).f q).app U = (Q).map (((PairOrdinaryForms.AffinePairOrdinaryForms.map R f).f q).app U) := by
  apply Eq.trans _ (congrArg (Q).map (PairOrdinaryForms.AffinePairOrdinaryForms.component R f q U)).symm
  change ((Q).map (𝟙 _) ≫ 𝟙 _) ≫
    (Q).map (OpenSectionPullback.DeRham.formsPullbackLE f U.unop.val.2.val U.unop.val.1.val U.unop.property q) ≫
      (𝟙 _ ≫ (Q).map (𝟙 _)) = _
  simp only [CategoryTheory.Functor.map_id, Category.comp_id, Category.id_comp]
  rfl

theorem original_component (q : ℕ) (U : (MapPairs.AffineMapPairs.Charts f.left)ᵒᵖ) :
    ((coordinateMap R f I).f q).app U =
      ((ProjectedCechTotal.ProjectedCechComplexPullback.pairedMap R f.left T S (PairOrdinaryPullback.AffinePairOrdinaryPullback.openMap R f)
        (originalMap R f I)).f q).app U :=
  (component R f I q U).trans
    ((congrArg (Q).map (PairOrdinaryForms.AffinePairOrdinaryForms.original_pullback R f q U)).trans ((Q).map_comp _ _))

theorem coordinates : coordinateMap R f I =
    ProjectedCechTotal.ProjectedCechComplexPullback.pairedMap R f.left T S (PairOrdinaryPullback.AffinePairOrdinaryPullback.openMap R f)
      (originalMap R f I) := by
  apply HomologicalComplex.Hom.ext
  funext q
  apply NatTrans.ext
  funext U
  exact original_component R f I q U

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Affine.PairQuotientPullback.AffinePairQuotientPullback
