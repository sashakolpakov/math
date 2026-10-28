import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.MarkedLevel
import OAI.NumberTheory.ArithmeticGroups.Diagonal

/-! # Fixed Basis -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.FixedBasis

noncomputable section

/-! Choose one basis of the original lattice for the entire reference
period family. Transporting this fixed basis to each fiber makes its
ordered finite-level labels independent of the tangent presentation. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ConstantSectionsOn.ConstantSections

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E]
    [NumberField.IsCMField E] {s : ℕ} (P : Datum.RankThreePELDatum E s)

namespace RankThreePELDatum

theorem _root_.OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum.zero_mem_domain (hP : P.IsAdmissible) : 0 ∈ P.domain := by
  have h := hP
  rcases h with ⟨_, _, _, hn, _⟩
  change (Geometry.ComplexBall.PrescribedSignsB.localB P.embeddings (Matrix.diagonal ![1, 1, P.b]) P.distinguished
    (Geometry.ComplexBall.PrescribedSignsB.lineVector 0) (star (Geometry.ComplexBall.PrescribedSignsB.lineVector 0))).re < 0
  simpa [NumberTheory.ArithmeticGroups.Diagonal.CongruenceLevel.localB_diagonal, Geometry.ComplexBall.PrescribedSignsB.lineVector, Datum.RankThreePELDatum.μ] using hn

def _root_.OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum.referenceOrigin (hP : P.IsAdmissible) : P.domain := ⟨0, P.zero_mem_domain hP⟩

theorem _root_.OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum.referenceBasis_nonempty (hP : P.IsAdmissible) :
    Nonempty (Module.Basis (Fin (2 * (3 * s))) ℤ P.lattice) := by
  let F := Fiber.referenceAnalyticFiber P hP (P.referenceOrigin hP)
  exact ⟨F.latticeBasis.map F.integralLatticeEquiv.symm⟩

def _root_.OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum.referenceBasis (hP : P.IsAdmissible) : Module.Basis (Fin (2 * (3 * s))) ℤ P.lattice :=
  Classical.choice (P.referenceBasis_nonempty hP)

def _root_.OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum.fixedLevelLabel (hP : P.IsAdmissible) (N : ℕ) (v : P.lattice) :
    Fin (2 * (3 * s)) → ZMod N := fun i => (P.referenceBasis hP).repr v i

theorem _root_.OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum.fixedLevelLabel_surjective (hP : P.IsAdmissible) (N : ℕ) :
    Function.Surjective (P.fixedLevelLabel hP N) := by
  intro a
  choose b hb using fun i => ZMod.intCast_surjective (a i)
  refine ⟨(P.referenceBasis hP).equivFun.symm b, ?_⟩
  funext i
  change (((P.referenceBasis hP).equivFun ((P.referenceBasis hP).equivFun.symm b) i : ℤ) : ZMod N) = a i
  rw [LinearEquiv.apply_symm_apply]
  exact hb i

end RankThreePELDatum

variable {P} {z : P.domain} {F : Fiber.ReferenceAnalyticFiber P z} {hP : P.IsAdmissible}

def _root_.OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.Fiber.ReferenceAnalyticFiber.fixedLatticeBasis (F : Fiber.ReferenceAnalyticFiber P z) (hP : P.IsAdmissible) :
    Module.Basis (Fin (2 * (3 * s))) ℤ F.periodData.periodIntegerLattice :=
  (P.referenceBasis hP).map F.integralLatticeEquiv

namespace ReferenceAlgebraicModel

local instance (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : IsIntegral A.toOver.left := A.variety.property
local instance (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : Smooth A.toOver.hom := A.variety.presentation.smooth

variable (M : AlgebraicModel.ReferenceAlgebraicModel F hP)

def _root_.OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.AlgebraicModel.ReferenceAlgebraicModel.fixedTorsionEquiv (N : ℕ) [NeZero N] : (Fin (2 * (3 * s)) → ZMod N) ≃+
    Additive (M.abelianScheme.torsionPoints N (ConstantSectionsOn.ConstantSections.baseTest Foundations.Scheme.ProjectiveSpace.complexBase)) :=
  (TorsionCongruence.TorusTorsion.latticeTorsionEquiv F.periodData.periodIntegerLattice (F.fixedLatticeBasis hP) N).trans
    ((TorsionCongruence.TorusTorsion.killedByEquiv M.periodAddEquiv N).trans
      (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.torsionAddEquiv M.abelianScheme N).symm)

theorem _root_.OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.AlgebraicModel.ReferenceAlgebraicModel.fixedTorsionEquiv_reference (N : ℕ) [NeZero N] (v : P.lattice) :
    (M.fixedTorsionEquiv N (P.fixedLevelLabel hP N v)).toMul.val =
      M.period (F.divisionPoint N v) := by
  have he := RepresentationTheory.Theta.Geometric.TorsionLabels.latticeTorsionEquiv_reference F.periodData.periodIntegerLattice
    (F.fixedLatticeBasis hP) N (F.integralLatticeEquiv v)
  have hl : (fun i => ((F.fixedLatticeBasis hP).repr (F.integralLatticeEquiv v) i : ZMod N)) =
      P.fixedLevelLabel hP N v := by
    funext i
    simp [Fiber.ReferenceAnalyticFiber.fixedLatticeBasis, Datum.RankThreePELDatum.fixedLevelLabel]
  rw [hl] at he
  exact congrArg M.period he

def _root_.OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.AlgebraicModel.ReferenceAlgebraicModel.fixedFullLevel (N : ℕ) [NeZero N] : M.abelianScheme.FullLevel N :=
  RepresentationTheory.Theta.Geometric.LevelLabels.relabelFullLevel M.abelianScheme (M.fullLevel N)
    (AddEquiv.toMultiplicativeLeft (M.fixedTorsionEquiv N))

theorem _root_.OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.AlgebraicModel.ReferenceAlgebraicModel.fixedFullLevel_reference (N : ℕ) [NeZero N] (v : P.lattice) :
    (((M.fixedFullLevel N).hom.app (.op (ConstantSectionsOn.ConstantSections.baseTest Foundations.Scheme.ProjectiveSpace.complexBase)))
      (LocallyConstant.const Foundations.Scheme.ProjectiveSpace.complexBase (Multiplicative.ofAdd (P.fixedLevelLabel hP N v)))).val =
        M.period (F.divisionPoint N v) := by
  have he := RepresentationTheory.Theta.Geometric.LevelLabels.relabelFullLevel_points M.abelianScheme (M.fullLevel N)
    (AddEquiv.toMultiplicativeLeft (M.fixedTorsionEquiv N))
  have hv := DFunLike.congr_fun he (Multiplicative.ofAdd (P.fixedLevelLabel hP N v))
  exact (congrArg Subtype.val hv).trans (M.fixedTorsionEquiv_reference N v)

end ReferenceAlgebraicModel

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.FixedBasis
