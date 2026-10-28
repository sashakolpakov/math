import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polarization.FiberComparison

/-! # Diagonal Line -/

namespace OAI.RepresentationTheory.Theta.Geometric.Relative.DiagonalLine

noncomputable section

/-! The actual Poincare bundle restricted along the polarization
diagonal is a line bundle on the total abelian scheme, and its fiber
is the diagonal of the original fiber biextension. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory

open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polarization.FiberComparison

variable {g : ℕ} {S T : Scheme.{0}} {A : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S}
    (D : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A) (p : A.scheme ⟶ D.abelian.scheme)

def relativeDiagonalLine : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.scheme.left :=
  D.poincare.pullback (lift p (𝟙 A.scheme)).left

theorem relativeDiagonal_fiber_square (s : T ⟶ S) :
    (lift (𝟙 (A.pullback s).scheme) (𝟙 (A.pullback s).scheme)).left ≫
      AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polarization.FiberComparison.polarizationBiextensionMap D p s =
    pullback.fst A.scheme.hom s ≫ (lift p (𝟙 A.scheme)).left := by
  let B := (A.pullback s).scheme
  have hdf : (lift (𝟙 B) (𝟙 B)).left ≫ pullback.fst B.hom B.hom = 𝟙 B.left :=
    congrArg Over.Hom.left (lift_fst (𝟙 B) (𝟙 B))
  have hds : (lift (𝟙 B) (𝟙 B)).left ≫ pullback.snd B.hom B.hom = 𝟙 B.left :=
    congrArg Over.Hom.left (lift_snd (𝟙 B) (𝟙 B))
  have hpf : (lift p (𝟙 A.scheme)).left ≫ pullback.fst D.abelian.scheme.hom A.scheme.hom = p.left :=
    congrArg Over.Hom.left (lift_fst p (𝟙 A.scheme))
  have hps : (lift p (𝟙 A.scheme)).left ≫ pullback.snd D.abelian.scheme.hom A.scheme.hom = 𝟙 A.scheme.left :=
    congrArg Over.Hom.left (lift_snd p (𝟙 A.scheme))
  apply Over.tensorObj_ext
  · simp only [Category.assoc, AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polarization.FiberComparison.polarizationBiextensionMap_fst, hpf]
    simpa only [Category.assoc, Category.id_comp] using
      congrArg (fun a => a ≫ pullback.fst A.scheme.hom s ≫ p.left) hdf
  · simp only [Category.assoc, AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polarization.FiberComparison.polarizationBiextensionMap_snd, hps, Category.comp_id]
    simpa only [Category.assoc, Category.id_comp] using
      congrArg (fun a => a ≫ pullback.fst A.scheme.hom s) hds

def relativeDiagonalLine_fiber_iso (s : T ⟶ S) :
    ((AlgebraicGeometry.AbelianModuli.HilbertConstruction.PolarizationData.polarizationBiextensionAt D p s).pullback
      (lift (𝟙 (A.pullback s).scheme) (𝟙 (A.pullback s).scheme)).left).sheaf ≅
        ((relativeDiagonalLine D p).pullback (pullback.fst A.scheme.hom s)).sheaf :=
  (Scheme.Modules.pullbackComp
    (lift (𝟙 (A.pullback s).scheme) (𝟙 (A.pullback s).scheme)).left
    (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polarization.FiberComparison.polarizationBiextensionMap D p s)).app D.poincare.sheaf ≪≫
    (Scheme.Modules.pullbackCongr (relativeDiagonal_fiber_square D p s)).app D.poincare.sheaf ≪≫
      (Scheme.Modules.pullbackComp (pullback.fst A.scheme.hom s) (lift p (𝟙 A.scheme)).left).symm.app D.poincare.sheaf

end

end OAI.RepresentationTheory.Theta.Geometric.Relative.DiagonalLine
