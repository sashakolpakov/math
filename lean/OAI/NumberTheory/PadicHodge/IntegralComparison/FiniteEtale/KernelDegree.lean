import OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Finite.EtaleGeometricCardinality
import OAI.NumberTheory.PadicHodge.IntegralComparison.Finite.FlatGenericDegree
import OAI.NumberTheory.PadicHodge.IntegralComparison.Geometric.TateModule
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.SmoothStalk

/-! # Kernel Degree -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.FiniteEtale.KernelDegree

noncomputable section

/-! The cardinality of the actual geometric point kernel of a finite
étale endomorphism is its native generic residue degree. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open MonoidalCategory
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme OAI.NumberTheory.PadicHodge.IntegralComparison.Geometric.TateModule

variable {k : Type} [Field k] [IsAlgClosed k]
  (A : Over (Spec (.of k))) [GrpObj A] [IsCommMonObj A]
  [Smooth A.hom] [GeometricallyIntegral A.hom]

local instance : IsIntegral A.left :=
  GeometricallyIntegral.isIntegral_of_subsingleton A.hom

def pointAction (f : A ⟶ A) [IsMonHom f] : Geometric.TateModule.Points A →+ Geometric.TateModule.Points A :=
  (AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme.pointsMap f (𝟙_ (Over (Spec (.of k))))).toAdditive

def kernelAdditiveEquiv (f : A ⟶ A) [IsMonHom f] :
    (AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme.pointsMap f (𝟙_ (Over (Spec (.of k))))).ker ≃ (pointAction A f).ker where
  toFun x := ⟨Additive.ofMul x.val, x.property⟩
  invFun x := ⟨x.val.toMul, x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

omit [IsCommMonObj A] in
theorem kernel_card (f : A ⟶ A) [IsMonHom f] [IsFinite f.left] [Etale f.left]
    [IsDominant f.left] :
    Nat.card (pointAction A f).ker = f.left.residueDegree (genericPoint A.left) := by
  let B := AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme.kernelObject f
  have : IsFinite B.hom := AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme.kernel_isFinite f
  have : Etale B.hom := by
    rw [AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme.kernel_hom_eq_snd]
    exact MorphismProperty.of_isPullback (P := @Etale) (AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme.kernel_isPullback f) inferInstance
  let x := IsLocalRing.closedPoint k
  calc
    Nat.card (pointAction A f).ker = Nat.card (Over.mk (𝟙 (Spec (.of k))) ⟶ B) := by
      exact (Nat.card_congr ((AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme.kernelPointsEquiv f (𝟙_ (Over (Spec (.of k))))).trans
        (kernelAdditiveEquiv A f))).symm
    _ = B.hom.finrank x := AlgebraicGeometry.PELModuli.IntegralModel.Finite.EtaleGeometricCardinality.finiteEtale_geometric_point_card B x
    _ = f.left.finrank (η[A].left x) := by
      rw [AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme.kernel_hom_eq_snd]
      exact Scheme.Hom.finrank_of_isPullback _ _ _ _ (AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme.kernel_isPullback f) x
    _ = f.left.finrank (genericPoint A.left) :=
      f.left.isLocallyConstant_finrank.apply_eq_of_preconnectedSpace _ _
    _ = f.left.residueDegree (genericPoint A.left) :=
      Finite.FlatGenericDegree.finiteFlat_finrank_generic_eq_residueDegree f.left (fun x => by
        have := AlgebraicGeometry.Quotients.FiniteDescent.SmoothStalk.Construction.SmoothStalkFactorial.stalk A.hom x
        infer_instance)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.FiniteEtale.KernelDegree
