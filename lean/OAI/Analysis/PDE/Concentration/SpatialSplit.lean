import OAI.Analysis.PDE.Concentration.SpatialHessian
import OAI.Analysis.PDE.Dirichlet.Periodic.Representatives

noncomputable section
namespace OAI.Analysis.PDE.Concentration

open Set Module OAI.Analysis.Calculus.Quaternion OAI.Analysis.PDE.Dirichlet OAI.Analysis.PDE.Green

/-- The actual physical spatial coordinates split into real periodic and
complex transverse coordinates. The periodic lattice may be any full basis
of the real factor, including a rotated side-100 lattice. -/
def physicalSpatialSplit (d : ℕ) : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 1) 3 ≃L[ℝ]
    ((Fin (d + 1) → ℝ) × (Option (Fin d) → ℂ)) :=
  LinearEquiv.toContinuousLinearEquiv {
    toEquiv := (OAI.Analysis.PDE.Green.physicalSpatialEquiv d).toEquiv
    map_add' := by
      intro x y
      change OAI.Analysis.PDE.Green.physicalSpatialEquiv d (x + y) = OAI.Analysis.PDE.Green.physicalSpatialEquiv d x + OAI.Analysis.PDE.Green.physicalSpatialEquiv d y
      apply Prod.ext
      · ext i
        simp only [Prod.fst_add, Pi.add_apply, OAI.Analysis.PDE.Green.physicalSpatialEquiv_fst, PiLp.add_apply]
      · simp only [Prod.snd_add, ← OAI.Analysis.PDE.Green.physicalSpatialProjection_eq, map_add]
    map_smul' := by
      intro c x
      change OAI.Analysis.PDE.Green.physicalSpatialEquiv d (c • x) = c • OAI.Analysis.PDE.Green.physicalSpatialEquiv d x
      apply Prod.ext
      · ext i
        change (OAI.Analysis.PDE.Green.physicalSpatialEquiv d (c • x)).1 i = c * (OAI.Analysis.PDE.Green.physicalSpatialEquiv d x).1 i
        simp only [OAI.Analysis.PDE.Green.physicalSpatialEquiv_fst, PiLp.smul_apply, smul_eq_mul]
      · change (OAI.Analysis.PDE.Green.physicalSpatialEquiv d (c • x)).2 = c • (OAI.Analysis.PDE.Green.physicalSpatialEquiv d x).2
        simp only [← OAI.Analysis.PDE.Green.physicalSpatialProjection_eq, map_smul]
  }

theorem physicalSpatialSplit_apply (d : ℕ) (x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 1) 3) :
    physicalSpatialSplit d x = OAI.Analysis.PDE.Green.physicalSpatialEquiv d x := rfl

theorem physicalSpatialSplit_snd (d : ℕ) (x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 1) 3) :
    (physicalSpatialSplit d x).2 = OAI.Analysis.PDE.Green.physicalSpatialProjection d x :=
  (OAI.Analysis.PDE.Green.physicalSpatialProjection_eq d x).symm

theorem physicalSpatialSplit_symm (d : ℕ) (x : Fin (d + 1) → ℝ)
    (q : Option (Fin d) → ℂ) :
    (physicalSpatialSplit d).symm (x, q) = OAI.Analysis.PDE.Green.physicalSpatialEmbedding d x q := rfl

/-- Every function of the transverse variables alone is periodic for every
physical real lattice. -/
theorem transverse_latticePeriodic {d : ℕ} {W : Type*}
    (b : Basis (Fin (d + 1)) ℝ (Fin (d + 1) → ℝ))
    (f : (Option (Fin d) → ℂ) → W) :
    OAI.Analysis.PDE.Dirichlet.LatticePeriodic (physicalSpatialSplit d) b (fun x => f (OAI.Analysis.PDE.Green.physicalSpatialProjection d x)) := by
  intro x l
  simp only [physicalSpatialSplit_symm, OAI.Analysis.PDE.Green.physicalSpatialProjection_embedding,
    physicalSpatialSplit_snd]

end OAI.Analysis.PDE.Concentration
