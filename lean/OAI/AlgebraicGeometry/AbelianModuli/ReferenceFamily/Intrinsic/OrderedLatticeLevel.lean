import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.MarkedLatticeIso
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Complex.ComplexLevel

/-! # Ordered Lattice Level -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.OrderedLatticeLevel

noncomputable section

/-! An actual ordered full level determines a canonical ordered
marking of the constructed integral Hermitian lattice modulo N.
Division by N and the original native exponential give the comparison. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.MarkedLatticeIso.IntrinsicPELMarking OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.Maps.IntrinsicAlgebraicMaps
open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ConstantSectionsOn.ConstantSections

variable {g N : ℕ} (A : HilbertConstruction.Abelian.Schemes.AbelianScheme g Foundations.Scheme.ProjectiveSpace.complexBase)
    (P : Foundations.Scheme.SmoothProjective.ProjectivePresentation A.scheme.left A.scheme.hom)

local instance : IsIntegral (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A P).toOver.left := (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A P).variety.property
local instance : Smooth (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A P).toOver.hom := (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A P).variety.presentation.smooth
local instance : IsProper (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A P).toOver.hom := (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A P).variety.presentation.projective.isProper

def nativeDivisionEquiv [NeZero N] :
    (HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A P) ⧸ LatticeDivision.TorusTorsion.multipleSubgroup (HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A P)) N) ≃+
      Additive (A.torsionPoints N (ConstantSectionsOn.ConstantSections.baseTest Foundations.Scheme.ProjectiveSpace.complexBase)) :=
  (LatticeDivision.TorusTorsion.latticeDivisionEquiv (HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A P)) N).trans
    ((TorsionCongruence.TorusTorsion.killedByEquiv (Maps.IntrinsicAlgebraicMaps.periodAddEquiv (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A P)) N).trans
      ((TorsionCongruence.TorusTorsion.killedByEquiv (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.nativePointEquiv A P).toAdditive N).trans (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.torsionAddEquiv A N).symm))

def orderedTorsionEquiv (α : A.FullLevel N) :
    (Fin (2 * g) → ZMod N) ≃+ Additive (A.torsionPoints N (ConstantSectionsOn.ConstantSections.baseTest Foundations.Scheme.ProjectiveSpace.complexBase)) :=
  ((Complex.ComplexLevel.constantValuesEquiv (Multiplicative (Fin (2 * g) → ZMod N))).trans
    ((α.app (.op (ConstantSectionsOn.ConstantSections.baseTest Foundations.Scheme.ProjectiveSpace.complexBase))).groupIsoToMulEquiv)).toAdditive

def nativeOrderedLatticeLevel [NeZero N] (α : A.FullLevel N) :
    (Fin (2 * g) → ZMod N) ≃+
      (HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A P) ⧸ LatticeDivision.TorusTorsion.multipleSubgroup (HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A P)) N) :=
  (orderedTorsionEquiv A α).trans (nativeDivisionEquiv A P).symm

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E]
    (ρ : ActionData.IntegralAction (NumberField.RingOfIntegers E) A)
    (s : ℕ) (hs : 0 < s) (hg : g = 3 * s) (hdegree : Module.finrank ℚ E = 2 * s)

def markedOrderedLatticeLevel [NeZero N] (α : A.FullLevel N) :
    (Fin (2 * g) → ZMod N) ≃+
      (PELMarking.IntrinsicPELMarking.markedLattice A P ρ s hs hg hdegree ⧸ LatticeDivision.TorusTorsion.multipleSubgroup (PELMarking.IntrinsicPELMarking.markedLattice A P ρ s hs hg hdegree) N) :=
  (nativeOrderedLatticeLevel A P α).trans
    (LatticeDivision.TorusTorsion.modNEquiv N (MarkedLatticeIso.IntrinsicPELMarking.nativeIntegralMarking A P ρ s hs hg hdegree).toAddEquiv)

theorem nativeDivisionEquiv_ordered [NeZero N] (α : A.FullLevel N) (c : Fin (2 * g) → ZMod N) :
    nativeDivisionEquiv A P (nativeOrderedLatticeLevel A P α c) =
      Additive.ofMul (α.hom.app (.op (ConstantSectionsOn.ConstantSections.baseTest Foundations.Scheme.ProjectiveSpace.complexBase))
        (LocallyConstant.const Foundations.Scheme.ProjectiveSpace.complexBase (Multiplicative.ofAdd c))) :=
  (nativeDivisionEquiv A P).apply_symm_apply _

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.OrderedLatticeLevel
