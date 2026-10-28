import OAI.AlgebraicGeometry.Picard.PoincareBundle.Recovered.ProductObject
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Bilinear.RecoveryEquation

/-! # Product Bilinear -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Recovered.ProductBilinear

noncomputable section

/-!
# Actual bilinear recovery of the retained quotient product
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Bilinear.BilinearPullback OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.KernelLinearization
open OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.CechInvariant OAI.AlgebraicGeometry.Picard.PoincareBundle.Ordinary.GlobalLineDescent

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffineHom f] [Flat f] [Surjective f] [IsLocallyNoetherian Y]
  (D : Geometric.KernelLinearization.modulePullbacks.DescentData (fun (_ : PUnit.{1}) => f))
  (hD : Line.Bundles.IsLine (D.obj PUnit.unit)) (M N P : Line.Bundles.LineBundle Y)
  {A B : X.Modules} (eM : (Scheme.Modules.pullback f).obj M.sheaf ≅ A)
  (eN : (Scheme.Modules.pullback f).obj N.sheaf ≅ B)
  (β : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap A B (D.obj PUnit.unit))
  (hβ : Bilinear.GlobalDescent.Compatible f D M N eM eN β)
  (eP : (Scheme.Modules.pullback f).obj P.sheaf ≅ D.obj PUnit.unit)
  (hP : (Scheme.Modules.pullback (pullback.fst f f)).map eP.hom ≫ (Geometric.CechInvariant.relationGluing f D).hom =
    (Cech.MateNormalization.standardGluing f (pullback.fst f f) (pullback.snd f f)
      pullback.condition).hom.app P.sheaf ≫ (Scheme.Modules.pullback (pullback.snd f f)).map eP.hom)

/-- The retained actual quotient product recovers the original bilinear operation through all three line isomorphisms. -/
theorem recovery_transport :
    Bilinear.Transport.transport
      (Bilinear.BilinearPullback.pullback f M.isLine N.isLine (ProductObject.recoveredProduct f D hD M N P eM eN β hβ eP hP).val)
      eM eN eP = β := by
  apply Bilinear.RecoveryEquation.recovery_transport
  exact (ProductObject.recoveredProduct f D hD M N P eM eN β hβ eP hP).property.1

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Recovered.ProductBilinear
