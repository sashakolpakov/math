import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.FrameInjective
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Cech.TotalQuasiIso

/-! # Frame Cech -/

namespace OAI

noncomputable section

namespace NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.FrameCech.Complexes

/-! Shared source and target complexes for the model-frame Cech comparison. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p]
  (n : ℕ) (X : Over (Spec (CommRingCat.of (Truncated.Witt.Ring p k n))))
  [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated]
  (Y : Over (Spec (CommRingCat.of k))) [IsSeparated Y.hom] (f : Y.left ⟶ X.left)
  (hp : IsPullback f Y.hom X.hom
    (Spec.map (CommRingCat.ofHom (Truncated.Witt.reduction p k n))))

local notation "Rcoeff" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := WittVector p k)
local notation "N" => OAI.NumberTheory.PadicHodge.IntegralComparison.NonemptyCechNerve.nerve (OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.CechSliceResolution.opens p k n X)

def cechFunctor : CochainComplex (X.left.affineOpensᵒᵖ ⥤ ModuleCat.{2} Rcoeff) ℕ ⥤
    HomologicalComplex₂ (ModuleCat.{2} Rcoeff) (.up ℕ) (.up ℕ) :=
  AlgebraicGeometry.Crystalline.Cohomology.Cech.TotalQuasiIso.CechTotalQuasiIso.bicomplex.{1, 2} Rcoeff N

def source : CochainComplex (ModuleCat.{2} Rcoeff) ℕ :=
  ((cechFunctor p k n X).obj
    (AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly.complex (.up ℕ) (FrameDiagonalMap.source p k n X Y f hp))).total (.up ℕ)

variable (J : InjectiveResolution (BoundedCrystalline.CrystallineCohomology.structureSheaf (p := p)
  (J := Ideal.span {(p : WittVector p k)}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k)
  (Witt.Crystalline.wittStructureMap p k Y) n))

def targetBicomplex : HomologicalComplex₂ (ModuleCat.{2} Rcoeff) (.up ℕ) (.up ℕ) :=
  (cechFunctor p k n X).obj
    (((SectionBifunctor.sections p k n X Y f).mapHomologicalComplex (.up ℕ)).obj J.cocomplex)

def target : CochainComplex (ModuleCat.{2} Rcoeff) ℕ :=
  (targetBicomplex p k n X Y f J).total (.up ℕ)

end NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.FrameCech.Complexes

namespace NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.FrameCech.Comparison

/-! The actual ramified frame de Rham diagram and original injective sections have quasi-isomorphic Cech totals in every degree. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite Simplicial

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p]
  (n : ℕ) (X : Over (Spec (CommRingCat.of (Truncated.Witt.Ring p k n))))
  [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated]
  (Y : Over (Spec (CommRingCat.of k))) [IsSeparated Y.hom] (f : Y.left ⟶ X.left)
  (hp : IsPullback f Y.hom X.hom
    (Spec.map (CommRingCat.ofHom (Truncated.Witt.reduction p k n))))

local notation "Rcoeff" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := WittVector p k)
local notation "U" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.CechSliceResolution.opens p k n X
local notation "N" => OAI.NumberTheory.PadicHodge.IntegralComparison.NonemptyCechNerve.nerve U

variable (J : InjectiveResolution (BoundedCrystalline.CrystallineCohomology.structureSheaf (p := p)
  (J := Ideal.span {(p : WittVector p k)}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k)
  (Witt.Crystalline.wittStructureMap p k Y) n))

def map : Complexes.source p k n X Y f hp ⟶
    Complexes.target p k n X Y f J :=
  AlgebraicGeometry.Crystalline.Cohomology.Cech.TotalQuasiIso.CechTotalQuasiIso.map.{1, 2} Rcoeff N
  (FrameInjective.Comparison.map p k n X Y f hp J)

theorem intersection_quasiIso (m : ℕ) (t : Fin (m + 1) → AlgebraicGeometry.Crystalline.Cohomology.Base.SmallEtaleCover.BaseSmallEtaleCover.Index (Truncated.Witt.Ring p k n) X) :
    QuasiIso ((((evaluation X.left.affineOpensᵒᵖ (ModuleCat.{2} Rcoeff)).obj
      (op (((N).obj (op ⦋m⦌)).obj t))).mapHomologicalComplex (.up ℕ)).map
        (FrameInjective.Comparison.map p k n X Y f hp J)) := by
  let I : X.left.affineOpens := ((N).obj (op ⦋m⦌)).obj t
  have hi : I.val ≤ (AlgebraicGeometry.Crystalline.Cohomology.Base.SmallEtaleCover.BaseSmallEtaleCover.opens (Truncated.Witt.Ring p k n) X (t 0)).val :=
    leOfHom (Pi.π (U ∘ t) 0)
  exact FrameInjective.Comparison.evaluation_quasiIso p k n X Y f hp J I (t 0) hi

theorem quasiIso : QuasiIso (Comparison.map p k n X Y f hp J) :=
  AlgebraicGeometry.Crystalline.Cohomology.Cech.TotalQuasiIso.CechTotalQuasiIso.quasiIso.{1, 2} Rcoeff N
    (FrameInjective.Comparison.map p k n X Y f hp J)
    (intersection_quasiIso p k n X Y f hp J)

end NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.FrameCech.Comparison

end

end OAI
