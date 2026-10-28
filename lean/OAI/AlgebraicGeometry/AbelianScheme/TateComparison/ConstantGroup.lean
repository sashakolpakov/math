import OAI.AlgebraicGeometry.PELModuli.IntegralModel.ConstantBaseChange
import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-! # Constant Group -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison.ConstantGroup

noncomputable section

/-! Constant commutative group schemes over fields are separated,
including groups with infinitely many labels. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.PELModuli.IntegralModel.ConstantBaseChange.ConstantGroupModels

theorem constantScheme_discrete (S : Scheme) [DiscreteTopology S] (I : Type) :
    DiscreteTopology (AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme S I).left :=
  (sigmaMk (fun _ : I => S)).discreteTopology

theorem constantFieldScheme_separated {k : Type} [Field k] (I : Type) :
    IsSeparated (AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme (Spec (.of k)) I).hom := by
  let S := Spec (.of k)
  let A := AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme S I
  have : DiscreteTopology S := inferInstanceAs (DiscreteTopology (PrimeSpectrum k))
  have : DiscreteTopology A.left := constantScheme_discrete S I
  have : DiscreteTopology (AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme A.left I).left := constantScheme_discrete A.left I
  let e : (AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme A.left I).left ≅ pullback A.hom A.hom :=
    (Over.forget A.left).mapIso (AbelianModuli.HilbertConstruction.Constant.BaseChange.constantSchemeBaseChangeIso A.hom I)
  have : DiscreteTopology (pullback A.hom A.hom : Scheme) := e.hom.homeomorph.discreteTopology
  have : IsOpenImmersion (pullback.diagonal A.hom) := inferInstance
  exact ⟨IsClosedImmersion.of_isPreimmersion (pullback.diagonal A.hom) (isClosed_discrete _)⟩

theorem constantGroup_commutative (S : Scheme) (G : Type) [CommGroup G] :
    IsCommMonObj (AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme S G) := by
  apply (isCommMonObj_iff_isMulCommutative _).mpr
  intro T
  constructor
  constructor
  intro f g
  let e := (PELModuli.IntegralModel.ConstantBaseChange.ConstantGroupModels.pointIso S G).app (.op T)
  apply (ConcreteCategory.bijective_of_isIso e.hom).1
  change e.hom.hom (f * g) = e.hom.hom (g * f)
  have hc : e.hom.hom f * e.hom.hom g = e.hom.hom g * e.hom.hom f :=
    @mul_comm (LocallyConstant T.left G) _ (e.hom.hom f) (e.hom.hom g)
  exact (e.hom.hom.map_mul f g).trans
    (hc.trans (e.hom.hom.map_mul g f).symm)

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison.ConstantGroup
