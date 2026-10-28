import OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.IsoRatios
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Tensor.CongrComposition
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Tensor.LineBundles

/-! # Line Iso Ratios -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.LineIsoRatios.PoincareBundle

noncomputable section

/-! Tensor products multiply the actual scalar ratios of line-bundle
isomorphisms on every scheme, including schemes with nilpotents. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ModuleScalar OAI.AlgebraicGeometry.Isogenies.NeighborCounting.LineEndomorphisms
open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.AutomorphismUnits OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.IsoRatios

variable {X : Scheme.{u}}

theorem tensorMap_scalarEnd (M N : X.Modules) (r s : Γ(X, ⊤)) :
    Picard.PoincareBundle.Tensor.SheafMaps.tensorMap (Isogenies.NeighborCounting.ModuleScalar.scalarEnd M r) (Isogenies.NeighborCounting.ModuleScalar.scalarEnd N s) =
      Isogenies.NeighborCounting.ModuleScalar.scalarEnd (ProductSheaf.tensorModule M N) (r * s) := by
  apply (Bilinear.Sheaves.SheafBilinearMap.tensorHomEquiv M N _).injective
  rw [Picard.PoincareBundle.Tensor.SheafMaps.tensorMap_bilinear, ← Picard.PoincareBundle.Tensor.SheafMaps.tensorBilinear_postcomp]
  ext U x y
  change (Picard.PoincareBundle.Tensor.SheafMaps.tensorBilinear M N).app U
      (X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op r • x)
      (X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op s • y) =
    X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op (r * s) •
      (Picard.PoincareBundle.Tensor.SheafMaps.tensorBilinear M N).app U x y
  simp only [map_mul, map_smul, LinearMap.smul_apply, mul_smul]
  exact smul_comm _ _ _

theorem tensor_scalarIso (M N : X.Modules) (r s : Γ(X, ⊤)ˣ) :
    ProductSheaf.tensorModuleCongr (Isogenies.NeighborCounting.ModuleScalar.scalarIso M r) (Isogenies.NeighborCounting.ModuleScalar.scalarIso N s) =
      Isogenies.NeighborCounting.ModuleScalar.scalarIso (ProductSheaf.tensorModule M N) (r * s) := by
  apply Iso.ext
  rw [Picard.PoincareBundle.Tensor.CongrMapComparison.congr_hom]
  exact tensorMap_scalarEnd M N r.val s.val

theorem unitOfAut_tensor {M N : X.Modules}
    (hM : ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.IsLineBundle M) (hN : ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.IsLineBundle N)
    (e : M ≅ M) (f : N ≅ N) :
    Picard.PoincareBundle.Line.AutomorphismUnits.unitOfAut (Picard.PoincareBundle.Tensor.LineBundles.tensor_isLine hM hN) (ProductSheaf.tensorModuleCongr e f) =
      Picard.PoincareBundle.Line.AutomorphismUnits.unitOfAut hM e * Picard.PoincareBundle.Line.AutomorphismUnits.unitOfAut hN f := by
  apply Units.ext
  apply Isogenies.NeighborCounting.LineEndomorphisms.scalarEnd_injective (Picard.PoincareBundle.Tensor.LineBundles.tensor_isLine hM hN)
  have ht := Picard.PoincareBundle.Line.AutomorphismUnits.scalarIso_unitOfAut (Picard.PoincareBundle.Tensor.LineBundles.tensor_isLine hM hN)
    (ProductSheaf.tensorModuleCongr e f)
  have he := Picard.PoincareBundle.Line.AutomorphismUnits.scalarIso_unitOfAut hM e
  have hf := Picard.PoincareBundle.Line.AutomorphismUnits.scalarIso_unitOfAut hN f
  have htf : ProductSheaf.tensorModuleCongr e f =
      Isogenies.NeighborCounting.ModuleScalar.scalarIso (ProductSheaf.tensorModule M N) (Picard.PoincareBundle.Line.AutomorphismUnits.unitOfAut hM e * Picard.PoincareBundle.Line.AutomorphismUnits.unitOfAut hN f) :=
    (congrArg₂ (fun a b => ProductSheaf.tensorModuleCongr a b) he hf).symm.trans
      (tensor_scalarIso M N (Picard.PoincareBundle.Line.AutomorphismUnits.unitOfAut hM e) (Picard.PoincareBundle.Line.AutomorphismUnits.unitOfAut hN f))
  exact congrArg Iso.hom (ht.trans htf)

theorem ratio_tensor {M M' N N' : X.Modules}
    (hM : ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.IsLineBundle M) (hN : ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.IsLineBundle N)
    (e e' : M ≅ M') (f f' : N ≅ N') :
    Picard.PoincareBundle.Line.IsoRatios.ratio (Picard.PoincareBundle.Tensor.LineBundles.tensor_isLine hM hN)
      (ProductSheaf.tensorModuleCongr e f) (ProductSheaf.tensorModuleCongr e' f') =
      Picard.PoincareBundle.Line.IsoRatios.ratio hM e e' * Picard.PoincareBundle.Line.IsoRatios.ratio hN f f' := by
  unfold Picard.PoincareBundle.Line.IsoRatios.ratio
  have hs : (ProductSheaf.tensorModuleCongr e' f').symm = ProductSheaf.tensorModuleCongr e'.symm f'.symm := by
    apply Iso.ext
    rfl
  rw [hs, Picard.PoincareBundle.Tensor.CongrComposition.trans]
  exact unitOfAut_tensor hM hN _ _

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.LineIsoRatios.PoincareBundle
