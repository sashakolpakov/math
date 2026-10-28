import OAI.AlgebraicGeometry.Picard.PoincareBundle.SharedRepresentation
import OAI.AlgebraicGeometry.Picard.PoincareBundle.PositiveScalar
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Product.Noetherian
import OAI.AlgebraicGeometry.Picard.PoincareBundle.TorsionHomomorphism

/-! # Shared Torsion Homomorphism -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.SharedTorsionHomomorphism

noncomputable section

/-!
# The quotient homomorphism from actual geometric dual data

The positive scalar cover and every Noetherian product condition are proved
from the original finite polarization and smooth proper group geometry.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

attribute [local instance] Over.cartesianMonoidalCategory

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplication OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Comparison.Bundle OAI.AlgebraicGeometry.Picard.PoincareBundle.FirstBiextensionFactor
open OAI.AlgebraicGeometry.Picard.PoincareBundle.Pulled.KernelFrames.Poincare OAI.AlgebraicGeometry.Picard.PoincareBundle.Poincare.TransverseFrames OAI.AlgebraicGeometry.Picard.PoincareBundle.Symmetric.MultiplicativeFrames
open OAI.AlgebraicGeometry.Picard.PoincareBundle.Biextension.Compatibility OAI.AlgebraicGeometry.Picard.PoincareBundle.SharedRepresentation

variable {k : Type u} [Field k] {A B : Over (Spec (.of k))}
  [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B]
  [Smooth A.hom] [IsProper A.hom] [GeometricallyConnected A.hom]
  [Smooth B.hom] [IsProper B.hom] [GeometricallyConnected B.hom]
  (DA : Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData A) (DB : Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData B)
  (ell : A ⟶ DA.abelian) [IsMonHom ell] [IsFinite ell.left]

variable (Dh : FiberwiseMultiplication.Multiplication (fst DA.abelian A) (snd DA.abelian A) (Line.Comparison.Bundle.fromShared DA.poincare))
  (Dv : FiberwiseMultiplication.Multiplication (snd DA.abelian A) (fst DA.abelian A) (Line.Comparison.Bundle.fromShared DA.poincare))
  (Qh : FiberwiseMultiplication.Multiplication (fst DB.abelian B) (snd DB.abelian B) (Line.Comparison.Bundle.fromShared DB.poincare))
  (Qv : FiberwiseMultiplication.Multiplication (snd DB.abelian B) (fst DB.abelian B) (Line.Comparison.Bundle.fromShared DB.poincare))
  (hi : Biextension.Compatibility.Interchange (Line.Comparison.Bundle.fromShared DA.poincare) Dh Dv) (n : ℕ) (hn : 0 < n)
  (e : (Scheme.Modules.pullback (β_ A A).hom.left).obj (FirstBiextensionFactor.familyLine (Line.Comparison.Bundle.fromShared DA.poincare) (ell ^ n)).sheaf ≅
    (FirstBiextensionFactor.familyLine (Line.Comparison.Bundle.fromShared DA.poincare) (ell ^ n)).sheaf)
  (hv : Symmetric.MultiplicativeFrames.secondMultiplication (FirstBiextensionFactor.familyLine (Line.Comparison.Bundle.fromShared DA.poincare) (ell ^ n)) (Pulled.KernelFrames.Poincare.sourceMultiplication (ell ^ n) (Line.Comparison.Bundle.fromShared DA.poincare) Dh) e =
    Poincare.TransverseFrames.sourceVertical (ell ^ n) (Line.Comparison.Bundle.fromShared DA.poincare) Dv)
  (hh : Symmetric.TransverseFrames.returnedFirst (FirstBiextensionFactor.familyLine (Line.Comparison.Bundle.fromShared DA.poincare) (ell ^ n)) (Poincare.TransverseFrames.sourceVertical (ell ^ n) (Line.Comparison.Bundle.fromShared DA.poincare) Dv) e =
    Pulled.KernelFrames.Poincare.sourceMultiplication (ell ^ n) (Line.Comparison.Bundle.fromShared DA.poincare) Dh)
  (f : A ⟶ B) [IsMonHom f] [IsFinite f.left] [Flat f.left] [Surjective f.left]
  (hker : ∀ (T : Over (Spec (.of k))) (x : T ⟶ A), x ≫ f = 1 → x ^ n = 1)

attribute [local instance] Kernel.Scheme.kernelGroup

variable (hlag : NaturalPairingOrthogonal.SelfAnnihilating (Kernel.ContainmentMap.torsionMap f n hker)
  (@TorsionPairing.Poincare.torsionPairing (Spec (.of k)) A DA.abelian
    inferInstance inferInstance DA.group DA.commutative ell inferInstance (Line.Comparison.Bundle.fromShared DA.poincare) Dh Dv n e
    (by exact hv) hi (by exact hh)))

include Dh Dv Qh Qv hi hn e hv hh hker hlag

/-- Actual geometric dual data and full-torsion self-annihilation construct the unique quotient homomorphism. -/
theorem existsUnique_homomorphism :
    ∃! m : B ⟶ DB.abelian, IsMonHom m ∧
      f ≫ m ≫ DualMaps.representedDualMap (SharedRepresentation.representation DA) (SharedRepresentation.representation DB) f = ell ^ n := by
  have : LocallyOfFiniteType (B ⊗ B).hom := Product.Noetherian.product_finiteType B B
  have : IsLocallyNoetherian (B ⊗ B).left := Product.Noetherian.product_noetherian B B
  have : IsLocallyNoetherian ((B ⊗ B) ⊗ B).left := Product.Noetherian.product_noetherian (B ⊗ B) B
  have : IsLocallyNoetherian (B ⊗ (B ⊗ B)).left := Product.Noetherian.product_noetherian B (B ⊗ B)
  have : EffectiveEpi ((𝟙 B) ^ n) := PositiveScalar.quotient_scalar_effective DA ell f n hn
  exact TorsionHomomorphism.Poincare.existsUnique_homomorphism ell (Line.Comparison.Bundle.fromShared DA.poincare) Dh Dv n e hv hi hh f hker hlag
    (Line.Comparison.Bundle.fromShared DB.poincare) Qh Qv (SharedRepresentation.representation DB)
    (SharedRepresentation.universalClass DB (Vertical.ProductParameters.globalProduct DB.abelian B (Line.Comparison.Bundle.fromShared DB.poincare) Qv)
      (Vertical.ProductParameters.globalProduct_isIso DB.abelian B (Line.Comparison.Bundle.fromShared DB.poincare) Qv))
    (SharedRepresentation.representation DA)
    (SharedRepresentation.universalClass DA (Vertical.ProductParameters.globalProduct DA.abelian A (Line.Comparison.Bundle.fromShared DA.poincare) Dv)
      (Vertical.ProductParameters.globalProduct_isIso DA.abelian A (Line.Comparison.Bundle.fromShared DA.poincare) Dv))

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.SharedTorsionHomomorphism
