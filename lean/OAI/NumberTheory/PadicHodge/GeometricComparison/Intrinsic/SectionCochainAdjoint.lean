import OAI.NumberTheory.PadicHodge.GeometricComparison.DeRham.Int
import OAI.NumberTheory.PadicHodge.GeometricComparison.Section.Hypercohomology

/-! # Section Cochain Adjoint -/

namespace OAI

noncomputable section

namespace NumberTheory.PadicHodge.GeometricComparison.Intrinsic.SectionCochainAdjoint.IntrinsicSectionPullback

/-! The native rank-one coefficient identification agrees with actual pullback of global sections. -/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry Opposite

variable {R : Type} [CommRing R] {X Y : Over (Spec (CommRingCat.of R))} (f : X ⟶ Y)

def map : Section.Hypercohomology.SectionHypercohomology.sections R (TopCat.of Y.left) ⟶
    DeRham.Int.inverseImage f ⋙ Section.Hypercohomology.SectionHypercohomology.sections R (TopCat.of X.left) where
  app F := ((DeRham.Int.imageAdjunction f).unit.app F).hom.app (op ⊤)
  naturality _ _ α := congrArg (fun k => k.hom.app (op ⊤)) ((DeRham.Int.imageAdjunction f).unit.naturality α)

theorem coefficient_homEquiv (F : AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.Sheaves R X)
    (g : AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.coefficientSheaf R X ⟶ F) :
    (constantSheafAdj (Opens.grothendieckTopology Y.left) (ModuleCat.{0} R) isTerminalTop).homEquiv
        (ModuleCat.of R R) ((DeRham.Int.directImage f).obj F)
        ((DeRham.Int.imageAdjunction f).homEquiv _ _ ((DeRham.Int.inverseImageConstantIso f).hom ≫ g)) =
      (constantSheafAdj (Opens.grothendieckTopology X.left) (ModuleCat.{0} R) isTerminalTop).homEquiv
        (ModuleCat.of R R) F g := by
  let a := constantSheafAdj (Opens.grothendieckTopology Y.left) (ModuleCat.{0} R) isTerminalTop
  let b := DeRham.Int.imageAdjunction f
  let c := constantSheafAdj (Opens.grothendieckTopology X.left) (ModuleCat.{0} R) isTerminalTop
  change (a.comp b).homEquiv _ _ ((DeRham.Int.inverseImageConstantIso f).hom ≫ g) = c.homEquiv _ _ g
  have h : (a.comp b).homEquiv _ _ (DeRham.Int.inverseImageConstantIso f).hom = c.unit.app (ModuleCat.of R R) :=
    Adjunction.homEquiv_leftAdjointUniq_hom_app (a.comp b) c (ModuleCat.of R R)
  have hu : c.homEquiv (ModuleCat.of R R) F g = c.unit.app (ModuleCat.of R R) ≫
      (Section.Hypercohomology.SectionHypercohomology.sections R (TopCat.of X.left)).map g := c.homEquiv_unit _ _ g
  exact ((a.comp b).homEquiv_naturality_right (DeRham.Int.inverseImageConstantIso f).hom g).trans
    ((congrArg (fun k => k ≫ (Section.Hypercohomology.SectionHypercohomology.sections R (TopCat.of X.left)).map g) h).trans hu.symm)

theorem coefficient_sections (F : AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.Sheaves R Y)
    (g : AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.coefficientSheaf R Y ⟶ F) :
    ConstantSheaf.ConstantSheafSections.linearEquiv R (TopCat.of X.left) ((DeRham.Int.inverseImage f).obj F)
        ((DeRham.Int.inverseImageConstantIso f).inv ≫ (DeRham.Int.inverseImage f).map g) =
      (IntrinsicSectionPullback.map f).app F (ConstantSheaf.ConstantSheafSections.linearEquiv R (TopCat.of Y.left) F g) := by
  let a := constantSheafAdj (Opens.grothendieckTopology Y.left) (ModuleCat.{0} R) isTerminalTop
  let b := DeRham.Int.imageAdjunction f
  let g' := (DeRham.Int.inverseImageConstantIso f).inv ≫ (DeRham.Int.inverseImage f).map g
  have h := coefficient_homEquiv f ((DeRham.Int.inverseImage f).obj F) g'
  have hc : (DeRham.Int.inverseImageConstantIso f).hom ≫ g' = (DeRham.Int.inverseImage f).map g :=
    (DeRham.Int.inverseImageConstantIso f).hom_inv_id_assoc _
  have hb : b.homEquiv _ _ ((DeRham.Int.inverseImage f).map g) = g ≫ b.unit.app F := by
    simpa only [Category.comp_id, b.homEquiv_id] using
      b.homEquiv_naturality_left g (𝟙 ((DeRham.Int.inverseImage f).obj F))
  erw [hc, hb, a.homEquiv_naturality_right g (b.unit.app F)] at h
  exact (congrArg (fun k => k 1) h).symm

end NumberTheory.PadicHodge.GeometricComparison.Intrinsic.SectionCochainAdjoint.IntrinsicSectionPullback

namespace NumberTheory.PadicHodge.GeometricComparison.Intrinsic.SectionCochainAdjoint.IntrinsicSectionCochainPullback

/-! The actual section pullback on nonnegative cochains is the global-section map of its direct-image adjoint. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

variable {R : Type} [CommRing R] {X Y : Over (Spec (CommRingCat.of R))} (f : X ⟶ Y)

local instance : (Section.Hypercohomology.SectionHypercohomology.sections R (TopCat.of X.left)).Additive where
  map_add := rfl
local instance : (Section.Hypercohomology.SectionHypercohomology.sections R (TopCat.of Y.left)).Additive where
  map_add := rfl

def map {K : CochainComplex (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.Sheaves R Y) ℕ} {L : CochainComplex (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.Sheaves R X) ℕ}
    (a : ((DeRham.Int.inverseImage f).mapHomologicalComplex (.up ℕ)).obj K ⟶ L) :
    ((Section.Hypercohomology.SectionHypercohomology.sections R (TopCat.of Y.left)).mapHomologicalComplex (.up ℕ)).obj K ⟶
      ((Section.Hypercohomology.SectionHypercohomology.sections R (TopCat.of X.left)).mapHomologicalComplex (.up ℕ)).obj L :=
  (NatTrans.mapHomologicalComplex (IntrinsicSectionPullback.map f) (.up ℕ)).app K ≫
    ((Section.Hypercohomology.SectionHypercohomology.sections R (TopCat.of X.left)).mapHomologicalComplex (.up ℕ)).map a

theorem map_eq_adjoint {K : CochainComplex (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.Sheaves R Y) ℕ}
    {L : CochainComplex (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.Sheaves R X) ℕ}
    (a : ((DeRham.Int.inverseImage f).mapHomologicalComplex (.up ℕ)).obj K ⟶ L) :
    IntrinsicSectionCochainPullback.map f a = ((Section.Hypercohomology.SectionHypercohomology.sections R (TopCat.of Y.left)).mapHomologicalComplex (.up ℕ)).map
      ((DeRham.Int.imageComplexAdjunction f).homEquiv K L a) := by
  have h := (DeRham.Int.imageComplexAdjunction f).homEquiv_unit K L a
  apply HomologicalComplex.Hom.ext
  funext n
  exact (congrArg (fun k => (k.f n).hom.app (op ⊤)) h).symm

end NumberTheory.PadicHodge.GeometricComparison.Intrinsic.SectionCochainAdjoint.IntrinsicSectionCochainPullback

end

end OAI
