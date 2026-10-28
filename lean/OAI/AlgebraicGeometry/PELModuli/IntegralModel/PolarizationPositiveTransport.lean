import OAI.AlgebraicGeometry.PELModuli.IntegralModel.PositiveBiextensionTransport
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.PolarizationBiextensionPairComparison
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.InverseLinePullback
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Finite.TypeGeometricPointLift

/-! # Polarization Positive Transport -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.PolarizationPositiveTransport

noncomputable section

/-! Geometric positivity is preserved by the actual two-family Poincare
comparison and reflected by a surjective base cover. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u
variable {S T : Scheme.{u}} {g : ℕ} {A B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S}

theorem positiveOnGeometricFiber_pairComparison
    (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A) (E : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData B)
    (p : A.scheme ⟶ D.abelian.scheme) (q : B.scheme ⟶ E.abelian.scheme)
    (eA : A.scheme ≅ B.scheme) (eD : D.abelian.scheme ≅ E.abelian.scheme) [IsMonHom eA.hom]
    (he : p ≫ eD.hom = eA.hom ≫ q)
    (hP : E.poincare.sheaf ≅ (D.poincare.pullback (eD.inv ⊗ₘ eA.inv).left).sheaf)
    {K : Type u} [Field K] [IsAlgClosed K] (s : Spec (.of K) ⟶ S)
    (h : AbelianModuli.HilbertConstruction.PolarizationData.PositiveOnGeometricFiber D p K s) : AbelianModuli.HilbertConstruction.PolarizationData.PositiveOnGeometricFiber E q K s := by
  let e : (A.pullback s).scheme ≅ (B.pullback s).scheme := (Over.pullback s).mapIso eA
  have : IsMonHom e.hom := inferInstanceAs (IsMonHom ((Over.pullback s).map eA.hom))
  exact PositiveBiextensionTransport.positiveBiextension_of_iso (X := (A.pullback s).scheme) (Y := (B.pullback s).scheme) e
    (AbelianModuli.HilbertConstruction.PolarizationData.polarizationBiextensionAt D p s) (AbelianModuli.HilbertConstruction.PolarizationData.polarizationBiextensionAt E q s)
    (PolarizationBiextensionPairComparison.polarizationBiextensionPairIso D E p q eA eD he hP s) h

theorem positiveOnGeometricFiber_of_pullback (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A)
    (p : A.scheme ⟶ D.abelian.scheme) (b : T ⟶ S)
    {K : Type u} [Field K] [IsAlgClosed K] (s : Spec (.of K) ⟶ T)
    (h : AbelianModuli.HilbertConstruction.PolarizationData.PositiveOnGeometricFiber (D.pullback b) ((Over.pullback b).map p) K s) :
    AbelianModuli.HilbertConstruction.PolarizationData.PositiveOnGeometricFiber D p K (s ≫ b) := by
  have : IsMonHom (A.pullbackCompIso b s).symm.hom :=
    inferInstanceAs (IsMonHom (A.pullbackCompIso b s).inv)
  exact PositiveBiextensionTransport.positiveBiextension_of_iso
    (X := ((A.pullback b).pullback s).scheme) (Y := (A.pullback (s ≫ b)).scheme)
    (A.pullbackCompIso b s).symm
    (AbelianModuli.HilbertConstruction.PolarizationData.polarizationBiextensionAt (D.pullback b) ((Over.pullback b).map p) s)
    (AbelianModuli.HilbertConstruction.PolarizationData.polarizationBiextensionAt D p (s ≫ b))
    (InverseLinePullback.inverseLinePullbackIso (A.fiberProductCompIso b s) _ _
      (AbelianModuli.HilbertConstruction.Polarization.FiberComparison.polarizationBiextensionCompIso D p b s)) h

theorem positiveOnGeometricFibers_of_baseChange (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A)
    (p : A.scheme ⟶ D.abelian.scheme) (b : T ⟶ S) [Surjective b] [LocallyOfFiniteType b]
    (h : ∀ (K : Type u) [Field K] [IsAlgClosed K] (s : Spec (.of K) ⟶ T),
      AbelianModuli.HilbertConstruction.PolarizationData.PositiveOnGeometricFiber (D.pullback b) ((Over.pullback b).map p) K s)
    (K : Type u) [Field K] [IsAlgClosed K] (s : Spec (.of K) ⟶ S) :
    AbelianModuli.HilbertConstruction.PolarizationData.PositiveOnGeometricFiber D p K s := by
  obtain ⟨t, ht⟩ := Finite.TypeGeometricPointLift.exists_geometric_point_lift b s
  subst s
  exact positiveOnGeometricFiber_of_pullback D p b t (h K t)

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.PolarizationPositiveTransport
