import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.GlobalDeRham
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.Principal
import OAI.NumberTheory.PadicHodge.GeometricComparison.ComplexAssemblyNatural

/-! # Ordinary Section Map -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.OrdinarySectionMap.Ordinary

noncomputable section

/-! The original frame comparison expressed on the ordinary de Rham
section diagram over the actual truncated base. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p]
  (n : ℕ) (X : Over (Spec (CommRingCat.of (Truncated.Witt.Ring p k n))))
  [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated]
  (Y : Over (Spec (CommRingCat.of k))) [IsSeparated Y.hom] (f : Y.left ⟶ X.left)
  (hp : IsPullback f Y.hom X.hom
    (Spec.map (CommRingCat.ofHom (Truncated.Witt.reduction p k n))))

abbrev coefficients : ModuleCat (Truncated.Witt.Ring p k n) ⥤
    ModuleCat.{2} (Crystalline.ExactRestriction.Coeff (B := WittVector p k)) :=
  ModuleCat.restrictScalars (algebraMap (WittVector p k) (Truncated.Witt.Ring p k n)) ⋙
    Principal.Comparison.coefficients p k

instance coefficients_additive : (coefficients p k n).Additive := by infer_instance

abbrev rawDiagram := OrdinaryBaseIso.Ordinary.target p k n X ⋙
  (Principal.Comparison.coefficients p k).mapHomologicalComplex (.up ℕ)

abbrev source := AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly.complex (.up ℕ) (rawDiagram p k n X)

def frameIso : AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly.complex (.up ℕ)
      (FrameDiagonalMap.source p k n X Y f hp) ≅ source p k n X :=
  (AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly.functor (.up ℕ)).mapIso
    (Functor.isoWhiskerRight (OrdinaryBaseIso.Ordinary.pdIso p k n X Y f hp)
      ((Principal.Comparison.coefficients p k).mapHomologicalComplex (.up ℕ)))

variable (I : InjectiveResolution (BoundedCrystalline.CrystallineCohomology.structureSheaf (p := p)
  (J := Ideal.span {(p : WittVector p k)}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k)
  (Witt.Crystalline.wittStructureMap p k Y) n))

def map : source p k n X ⟶
    ((SectionBifunctor.sections p k n X Y f).mapHomologicalComplex
      (.up ℕ)).obj I.cocomplex :=
  (frameIso p k n X Y f hp).inv ≫ FrameInjective.Comparison.map p k n X Y f hp I

theorem frame_map :
    (frameIso p k n X Y f hp).hom ≫ Ordinary.map p k n X Y f hp I =
      FrameInjective.Comparison.map p k n X Y f hp I := by
  rw [Ordinary.map, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.OrdinarySectionMap.Ordinary
