import OAI.AlgebraicGeometry.Quotients.FiniteDescent.GeometricCubeUniversal
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.CubeProductEq

/-! # Geometric Cube Is -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.GeometricCubeIs.Construction.GeometricCubeIdentity

noncomputable section

/-! The geometric cube identity for actual line bundles on a proper
smooth geometrically connected commutative group over an algebraically
closed field. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory
open scoped _root_.CategoryTheory.MonObj

universe u

variable {K : Type u} [Field K] [IsAlgClosed K] (A : Over (Spec (.of K)))
variable [GrpObj A] [IsCommMonObj A] [IsProper A.hom] [Smooth A.hom] [GeometricallyConnected A.hom]

theorem isCubical (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.left) : CubicalMultiplicationIs.Construction.CubicalMultiplication.IsCubical A L := by
  apply CubePicardFaces.Construction.CubePicardClass.isCubical A L
  intro a b c
  have h := congrArg (PicardPullbackId.Construction.PicardPullback.map (CubeProductEq.Construction.CubeProductLift.hom A a b c).left)
    (GeometricCubeUniversal.Construction.GeometricCubeClass.universal_class A L)
  rw [map_one, CubePicardValue.Construction.CubePicardClass.pullback, CubeProductEq.Construction.CubeProductLift.first_eq,
    CubeProductEq.Construction.CubeProductLift.second_eq, CubeProductEq.Construction.CubeProductLift.third_eq] at h
  exact h

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.GeometricCubeIs.Construction.GeometricCubeIdentity
