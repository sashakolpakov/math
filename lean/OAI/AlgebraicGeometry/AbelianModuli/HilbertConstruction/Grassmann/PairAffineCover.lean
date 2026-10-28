import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Grassmann.PairChartCover

/-! # Pair Affine Cover -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Grassmann

noncomputable section

/-! Every pair of Grassmannian maps has a common normalized chart cover by affine spectra. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {ι ν κ μ : Type u} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
variable {S : Scheme.{u}} {M : Over S}
variable {q : M ⟶ ParameterScheme.grassmannParameterScheme (ι := ι) (ν := ν) S}
variable {k : M ⟶ ParameterScheme.grassmannParameterScheme (ι := κ) (ν := μ) S}

variable (D : PairChartCover.GrassmannPairChartCover q k)

def PairChartCover.GrassmannPairChartCover.affineCover : M.left.OpenCover :=
  D.cover.bind (fun i => (D.cover.X i).affineOpenCover.openCover)

def PairChartCover.GrassmannPairChartCover.affineCoverProjection (i : D.cover.I₀) (j : (D.cover.X i).affineOpenCover.I₀) :
    Embedded.FamilyOpenCover.overOpenCoverObject M D.affineCover ⟨i, j⟩ ⟶ Embedded.FamilyOpenCover.overOpenCoverObject M D.cover i :=
  Over.homMk ((D.cover.X i).affineOpenCover.f j) (Category.assoc _ _ _).symm

theorem PairChartCover.GrassmannPairChartCover.affineCoverProjection_map (i : D.cover.I₀) (j : (D.cover.X i).affineOpenCover.I₀) :
    D.affineCoverProjection i j ≫ Embedded.FamilyOpenCover.overOpenCoverMap M D.cover i =
      Embedded.FamilyOpenCover.overOpenCoverMap M D.affineCover ⟨i, j⟩ := by
  apply Over.OverMorphism.ext
  rfl

def PairChartCover.GrassmannPairChartCover.affineRefinement : PairChartCover.GrassmannPairChartCover q k where
  cover := D.affineCover
  sourceColumns p := D.sourceColumns p.1
  targetColumns p := D.targetColumns p.1
  sourceLift p := D.affineCoverProjection p.1 p.2 ≫ D.sourceLift p.1
  targetLift p := D.affineCoverProjection p.1 p.2 ≫ D.targetLift p.1
  source_fac p := by
    exact (Category.assoc _ _ _).trans
      ((congrArg (fun h => D.affineCoverProjection p.1 p.2 ≫ h) (D.source_fac p.1)).trans
        ((Category.assoc _ _ _).symm.trans
          (congrArg (fun h => h ≫ q) (D.affineCoverProjection_map p.1 p.2))))
  target_fac p := by
    exact (Category.assoc _ _ _).trans
      ((congrArg (fun h => D.affineCoverProjection p.1 p.2 ≫ h) (D.target_fac p.1)).trans
        ((Category.assoc _ _ _).symm.trans
          (congrArg (fun h => h ≫ k) (D.affineCoverProjection_map p.1 p.2))))

def PairChartCover.GrassmannPairChartCover.affineCoverRing (p : D.affineCover.I₀) : CommRingCat.{u} :=
  (D.cover.X p.1).affineOpenCover.X p.2

theorem PairChartCover.GrassmannPairChartCover.affineCover_spec (p : D.affineCover.I₀) :
    D.affineCover.X p = Spec (D.affineCoverRing p) := rfl

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Grassmann
