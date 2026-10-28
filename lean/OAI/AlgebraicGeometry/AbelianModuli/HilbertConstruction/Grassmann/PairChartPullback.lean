import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Grassmann.PairChartCover

/-! # Pair Chart Pullback -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Grassmann

noncomputable section

/-! Pullback of a simultaneous Grassmannian chart cover along an arbitrary parameter morphism. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {S : Scheme.{u}} {M T : Over S}

def PairChartPullback.overOpenCoverPullbackProjection (f : T ⟶ M) (C : M.left.OpenCover) (i : C.I₀) :
    Embedded.FamilyOpenCover.overOpenCoverObject T (C.pullback₁ f.left) i ⟶ Embedded.FamilyOpenCover.overOpenCoverObject M C i :=
  ChartCover.overMorphismPullbackLift f (Embedded.FamilyOpenCover.overOpenCoverMap M C i)

theorem PairChartPullback.overOpenCoverPullbackProjection_fac (f : T ⟶ M) (C : M.left.OpenCover) (i : C.I₀) :
    PairChartPullback.overOpenCoverPullbackProjection f C i ≫ Embedded.FamilyOpenCover.overOpenCoverMap M C i =
      Embedded.FamilyOpenCover.overOpenCoverMap T (C.pullback₁ f.left) i ≫ f := by
  apply Over.OverMorphism.ext
  exact C.pullbackHom_map f.left i

variable {ι ν κ μ : Type u} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
variable {q : M ⟶ ParameterScheme.grassmannParameterScheme (ι := ι) (ν := ν) S}
variable {k : M ⟶ ParameterScheme.grassmannParameterScheme (ι := κ) (ν := μ) S}

def PairChartCover.GrassmannPairChartCover.pullback (D : PairChartCover.GrassmannPairChartCover q k) (f : T ⟶ M) :
    PairChartCover.GrassmannPairChartCover (f ≫ q) (f ≫ k) where
  cover := D.cover.pullback₁ f.left
  sourceColumns := D.sourceColumns
  targetColumns := D.targetColumns
  sourceLift i := PairChartPullback.overOpenCoverPullbackProjection f D.cover i ≫ D.sourceLift i
  targetLift i := PairChartPullback.overOpenCoverPullbackProjection f D.cover i ≫ D.targetLift i
  source_fac i := by
    let l := PairChartPullback.overOpenCoverPullbackProjection f D.cover i
    exact (Category.assoc _ _ _).trans
      ((congrArg (fun h => l ≫ h) (D.source_fac i)).trans
        ((Category.assoc _ _ _).symm.trans
          ((congrArg (fun h => h ≫ q) (PairChartPullback.overOpenCoverPullbackProjection_fac f D.cover i)).trans
            (Category.assoc _ _ _))))
  target_fac i := by
    let l := PairChartPullback.overOpenCoverPullbackProjection f D.cover i
    exact (Category.assoc _ _ _).trans
      ((congrArg (fun h => l ≫ h) (D.target_fac i)).trans
        ((Category.assoc _ _ _).symm.trans
          ((congrArg (fun h => h ≫ k) (PairChartPullback.overOpenCoverPullbackProjection_fac f D.cover i)).trans
            (Category.assoc _ _ _))))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Grassmann
