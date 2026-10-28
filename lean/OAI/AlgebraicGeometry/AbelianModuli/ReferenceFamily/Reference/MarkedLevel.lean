import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.AlgebraicModel
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.Discriminant
import OAI.RepresentationTheory.Theta.Geometric.TorsionLabels
import OAI.RepresentationTheory.Theta.Geometric.LevelLabels

/-! # Marked Level -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.MarkedLevel

noncomputable section

/-! Full ordered levels on the algebraized reference fiber carry the
original lattice labels. Their complex values are exactly the images
of the lattice vectors divided by the level. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ConstantSectionsOn.ConstantSections

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E]
    [NumberField.IsCMField E] {s : ℕ} {P : Datum.RankThreePELDatum E s}
    {z : P.domain} {F : Fiber.ReferenceAnalyticFiber P z} {hP : P.IsAdmissible}

local instance (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : IsIntegral A.toOver.left := A.variety.property
local instance (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : Smooth A.toOver.hom := A.variety.presentation.smooth

def _root_.OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.Fiber.ReferenceAnalyticFiber.referenceLabel (F : Fiber.ReferenceAnalyticFiber P z) (N : ℕ) (v : P.lattice) :
    Fin (2 * (3 * s)) → ZMod N := fun i => F.latticeBasis.repr (F.integralLatticeEquiv v) i

def _root_.OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.Fiber.ReferenceAnalyticFiber.divisionPoint (F : Fiber.ReferenceAnalyticFiber P z) (N : ℕ) (v : P.lattice) :
    F.periodData.periodTorus := QuotientAddGroup.mk ((N : ℝ)⁻¹ • F.periodEmbedding v.val)

namespace ReferenceAlgebraicModel

variable (M : AlgebraicModel.ReferenceAlgebraicModel F hP)

def _root_.OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.AlgebraicModel.ReferenceAlgebraicModel.periodAddEquiv : F.periodData.periodTorus ≃+
    Additive (M.abelianScheme.Points (ConstantSectionsOn.ConstantSections.baseTest Foundations.Scheme.ProjectiveSpace.complexBase)) where
  toFun t := Additive.ofMul (M.period t)
  invFun p := M.period.symm p.toMul
  left_inv := M.period.symm_apply_apply
  right_inv := M.period.apply_symm_apply
  map_add' := M.period_add

def _root_.OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.AlgebraicModel.ReferenceAlgebraicModel.markedTorsionEquiv (N : ℕ) [NeZero N] : (Fin (2 * (3 * s)) → ZMod N) ≃+
    Additive (M.abelianScheme.torsionPoints N (ConstantSectionsOn.ConstantSections.baseTest Foundations.Scheme.ProjectiveSpace.complexBase)) :=
  (TorsionCongruence.TorusTorsion.latticeTorsionEquiv F.periodData.periodIntegerLattice F.latticeBasis N).trans
    ((TorsionCongruence.TorusTorsion.killedByEquiv M.periodAddEquiv N).trans
      (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.torsionAddEquiv M.abelianScheme N).symm)

theorem _root_.OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.AlgebraicModel.ReferenceAlgebraicModel.markedTorsionEquiv_reference (N : ℕ) [NeZero N] (v : P.lattice) :
    (M.markedTorsionEquiv N (F.referenceLabel N v)).toMul.val = M.period (F.divisionPoint N v) := by
  have he := RepresentationTheory.Theta.Geometric.TorsionLabels.latticeTorsionEquiv_reference F.periodData.periodIntegerLattice
    F.latticeBasis N (F.integralLatticeEquiv v)
  change M.period ((TorsionCongruence.TorusTorsion.latticeTorsionEquiv F.periodData.periodIntegerLattice F.latticeBasis N
    (F.referenceLabel N v)).val) = _
  exact congrArg M.period he

def _root_.OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.AlgebraicModel.ReferenceAlgebraicModel.markedFullLevel (N : ℕ) [NeZero N] : M.abelianScheme.FullLevel N :=
  RepresentationTheory.Theta.Geometric.LevelLabels.relabelFullLevel M.abelianScheme (M.fullLevel N)
    (AddEquiv.toMultiplicativeLeft (M.markedTorsionEquiv N))

theorem _root_.OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.AlgebraicModel.ReferenceAlgebraicModel.markedFullLevel_reference (N : ℕ) [NeZero N] (v : P.lattice) :
    (((M.markedFullLevel N).hom.app (.op (ConstantSectionsOn.ConstantSections.baseTest Foundations.Scheme.ProjectiveSpace.complexBase)))
      (LocallyConstant.const Foundations.Scheme.ProjectiveSpace.complexBase (Multiplicative.ofAdd (F.referenceLabel N v)))).val =
        M.period (F.divisionPoint N v) := by
  have he := RepresentationTheory.Theta.Geometric.LevelLabels.relabelFullLevel_points M.abelianScheme (M.fullLevel N)
    (AddEquiv.toMultiplicativeLeft (M.markedTorsionEquiv N))
  have hv := DFunLike.congr_fun he (Multiplicative.ofAdd (F.referenceLabel N v))
  exact (congrArg Subtype.val hv).trans (M.markedTorsionEquiv_reference N v)

end ReferenceAlgebraicModel

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.MarkedLevel
