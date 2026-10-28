import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.FrameDiagonalIso
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.DiagonalCech
import OAI.NumberTheory.PadicHodge.GeometricComparison.QuasiIsoLeft

/-! # Frame Injective -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.FrameInjective.Comparison

noncomputable section

/-! The actual native frame de Rham diagram maps to the original global
injective-resolution sections, with local quasi-isomorphism on the coordinate cover. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p]
  (n : ℕ) (X : Over (Spec (CommRingCat.of (Truncated.Witt.Ring p k n))))
  [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated]
  (Y : Over (Spec (CommRingCat.of k))) [IsSeparated Y.hom] (f : Y.left ⟶ X.left)
  (hp : IsPullback f Y.hom X.hom
    (Spec.map (CommRingCat.ofHom (Truncated.Witt.reduction p k n))))

local notation "Rcoeff" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := WittVector p k)
local notation "S" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.SectionBifunctor.sections p k n X Y f

variable (J : InjectiveResolution (BoundedCrystalline.CrystallineCohomology.structureSheaf (p := p)
  (J := Ideal.span {(p : WittVector p k)})
  (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k)
  (Witt.Crystalline.wittStructureMap p k Y) n))

def map : AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly.complex (.up ℕ) (FrameDiagonalMap.source p k n X Y f hp) ⟶
    ((S).mapHomologicalComplex (.up ℕ)).obj J.cocomplex :=
  FrameDiagonalMap.map p k n X Y f hp ≫ DiagonalCech.Comparison.map p k n X Y f hp J

variable (I : X.left.affineOpens) (i : AlgebraicGeometry.Crystalline.Cohomology.Base.SmallEtaleCover.BaseSmallEtaleCover.Index (Truncated.Witt.Ring p k n) X)
  (hi : I.val ≤ (AlgebraicGeometry.Crystalline.Cohomology.Base.SmallEtaleCover.BaseSmallEtaleCover.opens (Truncated.Witt.Ring p k n) X i).val)

include hi in
theorem evaluation_quasiIso : QuasiIso
    (((DiagonalCech.Comparison.evaluate p k n X I).mapHomologicalComplex (.up ℕ)).map
      (Comparison.map p k n X Y f hp J)) := by
  let ha : IsIso ((FrameDiagonalMap.transformation p k n X Y f hp).app (op I)) :=
    FrameDiagonalIso.isIso p k n X Y f hp I i hi
  let hb := DiagonalCech.Comparison.evaluation_quasiIso p k n X Y f hp J I i hi
  change QuasiIso ((FrameDiagonalMap.transformation p k n X Y f hp).app (op I) ≫
    (((DiagonalCech.Comparison.evaluate p k n X I).mapHomologicalComplex (.up ℕ)).map
      (DiagonalCech.Comparison.map p k n X Y f hp J)))
  exact GeometricComparison.QuasiIsoLeft.QuasiIsoComposeIsomorphism.left _ _ ha hb

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.FrameInjective.Comparison
