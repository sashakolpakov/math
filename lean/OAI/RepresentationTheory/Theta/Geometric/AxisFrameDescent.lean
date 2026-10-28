import OAI.RepresentationTheory.Theta.Geometric.FramedDescent
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Ordinary.SquareGluing

/-! # Axis Frame Descent -/

namespace OAI.RepresentationTheory.Theta.Geometric.AxisFrameDescent

noncomputable section

/-! An invariant axis frame descends through a commuting square of
faithfully flat covers, using the full ordinary descent categories. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.KernelLinearization OAI.AlgebraicGeometry.Picard.PoincareBundle.Ordinary.SquareGluing
universe u

variable {X Y X' Y' : Scheme.{u}} (f : X ⟶ Y) (f' : X' ⟶ Y')
    (i : X' ⟶ X) (j : Y' ⟶ Y) (hf : i ≫ f = f' ≫ j)
    (D : AlgebraicGeometry.Picard.PoincareBundle.Geometric.KernelLinearization.modulePullbacks.DescentData (fun (_ : PUnit.{1}) => f))
    (e : (Scheme.Modules.pullback i).obj (D.obj PUnit.unit) ≅ AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj X')
    (he : ∀ {T : Scheme.{u}} (q : T ⟶ Y') (x y : T ⟶ X')
      (hx : x ≫ f' = q) (hy : y ≫ f' = q),
      D.hom (q ≫ j) (i₁ := PUnit.unit) (i₂ := PUnit.unit) (x ≫ i) (y ≫ i)
        (by rw [Category.assoc, hf, ← Category.assoc, hx])
        (by rw [Category.assoc, hf, ← Category.assoc, hy]) ≫
          (FactoredPullbackFrames.factoredPullbackFrame y i e).hom = (FactoredPullbackFrames.factoredPullbackFrame x i e).hom)

def axisFramedDatumIso :
    AlgebraicGeometry.Picard.PoincareBundle.Ordinary.SquareGluing.pulledDatum f f' i j hf D ≅
      (AlgebraicGeometry.Picard.PoincareBundle.Geometric.KernelLinearization.modulePullbacks.toDescentData (fun (_ : PUnit.{1}) => f')).obj (AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj Y') := by
  apply FramedDescent.framedDatumIso f' (AlgebraicGeometry.Picard.PoincareBundle.Ordinary.SquareGluing.pulledDatum f f' i j hf D) e
  intro T q x y hx hy
  rw [AlgebraicGeometry.Picard.PoincareBundle.Ordinary.SquareGluing.pulledHom]
  change ((Scheme.Modules.pullbackComp x i).app (D.obj PUnit.unit)).hom ≫
      (D.hom (q ≫ j) (i₁ := PUnit.unit) (i₂ := PUnit.unit) (x ≫ i) (y ≫ i) _ _ ≫ (FactoredPullbackFrames.factoredPullbackFrame y i e).hom) = _
  rw [he q x y hx hy]
  simp only [FactoredPullbackFrames.factoredPullbackFrame, Iso.trans_hom, Iso.symm_hom, Iso.hom_inv_id_assoc]

include e he in
theorem pullbackLine_trivial_of_normalized_datum
    [IsAffineHom f'] [Flat f'] [Surjective f'] [IsLocallyNoetherian Y']
    (Q : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle Y)
    (recover : (AlgebraicGeometry.Picard.PoincareBundle.Geometric.KernelLinearization.modulePullbacks.toDescentData (fun (_ : PUnit.{1}) => f)).obj Q.sheaf ≅ D) :
    Nonempty ((Q.pullback j).sheaf ≅ AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y') := by
  let P := Pseudofunctor.DescentData.pullFunctor AlgebraicGeometry.Picard.PoincareBundle.Geometric.KernelLinearization.modulePullbacks
    (f := fun (_ : PUnit.{1}) => f) (f' := fun (_ : PUnit.{1}) => f') (p := j)
    (α := fun (_ : PUnit.{1}) => PUnit.unit) (p' := fun (_ : PUnit.{1}) => i) (fun _ => hf)
  let c := (Pseudofunctor.DescentData.toDescentDataCompPullFunctorIso AlgebraicGeometry.Picard.PoincareBundle.Geometric.KernelLinearization.modulePullbacks
    (f := fun (_ : PUnit.{1}) => f) (f' := fun (_ : PUnit.{1}) => f') (p := j)
    (α := fun (_ : PUnit.{1}) => PUnit.unit) (p' := fun (_ : PUnit.{1}) => i)
    (fun _ => hf)).app Q.sheaf
  exact FramedDescent.lineIso_of_descentIso f' (Q.pullback j) (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.trivial Y')
    (c.symm ≪≫ P.mapIso recover ≪≫ axisFramedDatumIso f f' i j hf D e he)

end

end OAI.RepresentationTheory.Theta.Geometric.AxisFrameDescent
