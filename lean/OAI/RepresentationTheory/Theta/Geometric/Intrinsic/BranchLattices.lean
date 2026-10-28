import OAI.RepresentationTheory.Theta.Geometric.Intrinsic.ClearedBranchFibers
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.CorrespondencePointBaseChange
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.ConcreteBranchLatticeEquiv

/-! # Branch Lattices -/

namespace OAI.RepresentationTheory.Theta.Geometric

noncomputable section

/-! Original continuous cleared branches retain TateComparison's actual source
fibers and chosen Tate lattices, through the literal base-change map. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry OAI.AlgebraicGeometry.AbelianScheme.TateComparison.CorrespondencePointBaseChange

theorem Intrinsic.BranchLattices.padicTateComparisonLatticeInput (q : ℕ) [Fact q.Prime] : AlgebraicGeometry.AbelianScheme.TateComparison.Duality.ElementaryDivisorsInput ℤ_[q] ℚ_[q] := by
  intro n π hπ L M hL hM
  let : Submodule.IsLattice ℚ_[q] L := hL
  let : Submodule.IsLattice ℚ_[q] M := hM
  exact Algebra.Modules.ElementaryDivisors.lattices_elementary_divisors π hπ L M

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
    {Index Ga MpR MpF MpA : Type} [Fintype Index] [DecidableEq Index]
    [Group Ga] [TopologicalSpace Ga] [Group MpR] [Group MpF] [Group MpA]
    (D : Data.ActiveHeckeThetaData E K s q Index Ga MpR MpF MpA)

def Data.ActiveHeckeThetaData.branchGenericPoint (c : D.domain → AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints D.pel.complexSpace)
    (x₀ : D.domain) : D.pel.GeometricPoint (𝟙 AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase ≫ D.pel.complexGenericPoint) :=
  AlgebraicGeometry.AbelianScheme.TateComparison.FieldPointTransport.pointBaseChangeEquiv D.pel.complexGenericPoint (𝟙 AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase)
    (𝟙 AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase ≫ D.pel.complexGenericPoint) rfl D.pel.space (c x₀)

def Data.ActiveHeckeThetaData.nativeClearedBranchGenericFiberEquiv (hg : D.pel.HasIntegralModelGeometry)
    {c : D.domain → AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints D.pel.complexSpace} (hc : Continuous c)
    (a : Intrinsic.Hecke.ActiveWeight) (x₀ : D.domain) : D.ClearedBranch c a ≃
    (D.pel.correspondence (Intrinsic.Hecke.clearedActiveType D.pel.reference.distinguished a)).Fiber
      (D.branchGenericPoint c x₀) :=
  (D.nativeClearedBranchFiberEquiv hg hc a x₀).trans
    ((D.pel.correspondence (Intrinsic.Hecke.clearedActiveType D.pel.reference.distinguished a)).baseChangeFiberEquiv
      D.pel.complexGenericPoint (𝟙 AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) (c x₀))

def Data.ActiveHeckeThetaData.nativeClearedBranchLatticeEquiv (hg : D.pel.HasIntegralModelGeometry)
    (hgood : D.pel.IsGoodCompletelySplitPrime) (hIsogenyQuotient : D.pel.RealizesIsogenyQuotient)
    (hdegree : Module.finrank ℚ E = 2 * s) (hs : 0 < s)
    {c : D.domain → AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints D.pel.complexSpace} (hc : Continuous c)
    (a : Intrinsic.Hecke.ActiveWeight) (x₀ : D.domain)
    (frame : D.pel.FiberFrame (𝟙 AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase ≫ D.pel.complexGenericPoint) (D.branchGenericPoint c x₀))
    (hframe : AlgebraicGeometry.AbelianScheme.TateComparison.Rational.IsSplitActionFrame
      (D.pel.fiberFamily (𝟙 AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase ≫ D.pel.complexGenericPoint) (D.branchGenericPoint c x₀))
      (Over.mk (𝟙 AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase)) q D.pel.localCharacter frame) :
    D.ClearedBranch c a ≃ D.pel.BranchLatticeChoices (D.branchGenericPoint c x₀) frame
      (Intrinsic.Hecke.clearedActiveType D.pel.reference.distinguished a) :=
  (D.nativeClearedBranchGenericFiberEquiv hg hc a x₀).trans
    (D.pel.c46BranchLatticeEquiv (D.branchGenericPoint c x₀) frame hIsogenyQuotient
      (Intrinsic.Hecke.clearedActiveType D.pel.reference.distinguished a) hgood hg hframe
      (Intrinsic.BranchLattices.padicTateComparisonLatticeInput q) hdegree hs)

theorem Data.ActiveHeckeThetaData.nativeClearedBranchLatticeEquiv_lattice (hg : D.pel.HasIntegralModelGeometry)
    (hgood : D.pel.IsGoodCompletelySplitPrime) (hIsogenyQuotient : D.pel.RealizesIsogenyQuotient)
    (hdegree : Module.finrank ℚ E = 2 * s) (hs : 0 < s)
    {c : D.domain → AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints D.pel.complexSpace} (hc : Continuous c)
    (a : Intrinsic.Hecke.ActiveWeight) (x₀ : D.domain)
    (frame : D.pel.FiberFrame (𝟙 AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase ≫ D.pel.complexGenericPoint) (D.branchGenericPoint c x₀))
    (hframe : AlgebraicGeometry.AbelianScheme.TateComparison.Rational.IsSplitActionFrame
      (D.pel.fiberFamily (𝟙 AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase ≫ D.pel.complexGenericPoint) (D.branchGenericPoint c x₀))
      (Over.mk (𝟙 AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase)) q D.pel.localCharacter frame)
    (b : D.ClearedBranch c a) (v : Fin s) :
    ((D.nativeClearedBranchLatticeEquiv hg hgood hIsogenyQuotient hdegree hs hc a x₀ frame hframe b v).val).val =
      D.pel.c46ChosenBranchLattices (D.branchGenericPoint c x₀) frame hIsogenyQuotient
        (Intrinsic.Hecke.clearedActiveType D.pel.reference.distinguished a)
        (D.nativeClearedBranchGenericFiberEquiv hg hc a x₀ b) v :=
  D.pel.c46BranchLatticeEquiv_lattice (D.branchGenericPoint c x₀) frame hIsogenyQuotient
    (Intrinsic.Hecke.clearedActiveType D.pel.reference.distinguished a) hgood hg hframe
    (Intrinsic.BranchLattices.padicTateComparisonLatticeInput q) hdegree hs _ v

end

end OAI.RepresentationTheory.Theta.Geometric
