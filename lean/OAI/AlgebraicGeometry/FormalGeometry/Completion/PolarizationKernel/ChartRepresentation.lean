import OAI.AlgebraicGeometry.FormalGeometry.Completion.PolarizationKernel.KernelSheaf
import OAI.AlgebraicGeometry.FormalGeometry.Completion.PolarizationKernel.Functor
import OAI.AlgebraicGeometry.FormalGeometry.Completion.SubfunctorChart

/-! # Chart Representation -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.PolarizationKernel.ChartRepresentation

noncomputable section

/-! The derived finite-type kernel chart is the actual pullback of
the polarization-kernel sheaf along its parameter morphism. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory Opposite
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

namespace Construction

universe u
variable {K : Type u} [Field K] [IsAlgClosed K]
  (A : Over (Spec (CommRingCat.of K))) [GrpObj A] [IsCommMonObj A]
  [IsProper A.hom] [Smooth A.hom] [GeometricallyIntegral A.hom]
  (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.left) {T : Over (Spec (CommRingCat.of K))}
  [IsAffine T.left] [IsNoetherianRing Γ(T.left, ⊤)] (a : T ⟶ A)

theorem polarizationKernelChart_factorization (U : Over (Spec (CommRingCat.of K))) (j : U ⟶ T) :
    (j ≫ a) ∈ (Functor.Construction.polarizationKernelSubfunctor A L).obj (op U) ↔
      ∃ z : U ⟶ FamilyLiftFactorization.Construction.compositeFamily T (Chart.Construction.polarizationKernelChart A L a),
        z ≫ FamilyLiftFactorization.Construction.compositeFamilyMap T (Chart.Construction.polarizationKernelChart A L a) = j := by
  change Polarization.PicardMap.Construction.polarizationRelativeSection A L (j ≫ a) = AbelianModuli.HilbertConstruction.Picard.PicardSheaf.trivialPicardClass A U ↔ _
  rw [← KernelSheaf.Construction.polarizationKernelChart_hasLift_iff_relative_zero A L a j]
  constructor
  · rintro ⟨p⟩
    let z := FamilyLiftFactorization.Construction.familyLiftFactorizationEquiv T (Chart.Construction.polarizationKernelChart A L a) j p
    exact ⟨z.val, z.property⟩
  · rintro ⟨z, hz⟩
    exact ⟨(FamilyLiftFactorization.Construction.familyLiftFactorizationEquiv T (Chart.Construction.polarizationKernelChart A L a) j).symm ⟨z, hz⟩⟩

def polarizationKernelChartMap :
    yoneda.obj (FamilyLiftFactorization.Construction.compositeFamily T (Chart.Construction.polarizationKernelChart A L a)) ⟶ (Functor.Construction.polarizationKernelSubfunctor A L).toFunctor :=
  SubfunctorChart.Construction.subfunctorChartMap (Functor.Construction.polarizationKernelSubfunctor A L) a
    (FamilyLiftFactorization.Construction.compositeFamilyMap T (Chart.Construction.polarizationKernelChart A L a)) (polarizationKernelChart_factorization A L a)

theorem polarizationKernelChart_isPullback :
    IsPullback (yoneda.map (FamilyLiftFactorization.Construction.compositeFamilyMap T (Chart.Construction.polarizationKernelChart A L a)))
      (polarizationKernelChartMap A L a) (yoneda.map a) (Functor.Construction.polarizationKernelSubfunctor A L).ι :=
  SubfunctorChart.Construction.subfunctorChart_isPullback (Functor.Construction.polarizationKernelSubfunctor A L) a
    (FamilyLiftFactorization.Construction.compositeFamilyMap T (Chart.Construction.polarizationKernelChart A L a)) (polarizationKernelChart_factorization A L a)

end Construction

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.PolarizationKernel.ChartRepresentation
