import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.IsogenyQuotient
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Rational
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Duality

/-! # Geometric Flags -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison

noncomputable section

/-! Actual geometric flags, their marked polarized composite isogenies,
and their intrinsic Tate lattices. Existence of a comparison with ordinary
linear flags is a conclusion to prove, not part of the input record. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj TensorProduct Pointwise

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  (D : Data.SphericalPELAlbaneseData E K s q)
  {k : Type} [Field k] [IsAlgClosed k] (b : Spec (.of k) ⟶ Spec (.of K))

abbrev Data.SphericalPELAlbaneseData.GeometricPoint := Over.mk b ⟶ D.space

/-- The PEL fiber is the actual pullback along the geometric point. -/
def Data.SphericalPELAlbaneseData.fiberFamily (x : D.GeometricPoint b) :
    PEL.PELFamilyData (NumberField.RingOfIntegers E) (3 * s) D.level (Spec (.of k)) :=
  D.family.pullback x.left

/-- A geometric flag retains each cover point, rather than only its target. -/
structure Data.SphericalPELAlbaneseData.PELFlag (x : D.GeometricPoint b) (ts : List (Local.IntegralType s)) where
  point : Fin (ts.length + 1) → D.GeometricPoint b
  start : point 0 = x
  branch : ∀ j : Fin ts.length, Over.mk b ⟶ (D.correspondence (ts.get j)).cover
  source : ∀ j, branch j ≫ (D.correspondence (ts.get j)).source = point j.castSucc
  target : ∀ j, branch j ≫ (D.correspondence (ts.get j)).target = point j.succ

abbrev Data.SphericalPELAlbaneseData.FiberFrame (x : D.GeometricPoint b) :=
  Rational.SplitTateFrame s (D.fiberFamily b x).abelian.scheme (Over.mk (𝟙 (Spec (.of k)))) q

abbrev Data.SphericalPELAlbaneseData.flagMultiplier (ts : List (Local.IntegralType s)) (j : Fin (ts.length + 1)) :=
  (Local.cumulativeMultiplier ts j).toNat

variable {b} {x : D.GeometricPoint b} {ts : List (Local.IntegralType s)}

/-- Candidate actual composites at all stages, with their polarization
factors and transported full markings. No composition law is a field. -/
abbrev Data.SphericalPELAlbaneseData.CompositeSystem (F : D.PELFlag b x ts) :=
  ∀ j : Fin (ts.length + 1), PELIsogenies.PELIsogeny (D.fiberFamily b x)
    (D.fiberFamily b (F.point j)) (q ^ Data.SphericalPELAlbaneseData.flagMultiplier ts j)

abbrev Data.SphericalPELAlbaneseData.StepSystem (F : D.PELFlag b x ts) :=
  ∀ j : Fin ts.length, PELIsogenies.PELIsogeny (D.fiberFamily b (F.point j.castSucc))
    (D.fiberFamily b (F.point j.succ)) (q ^ (ts.get j).multiplierNat)

/-- A genuine polarized marked composite, retaining its actual target. -/
abbrev Data.SphericalPELAlbaneseData.CompositeDatum (x : D.GeometricPoint b) (ts : List (Local.IntegralType s)) :=
  Σ y : D.GeometricPoint b, PELIsogenies.PELIsogeny (D.fiberFamily b x)
    (D.fiberFamily b y) (q ^ Data.SphericalPELAlbaneseData.flagMultiplier ts (Fin.last ts.length))

def Data.SphericalPELAlbaneseData.finalComposite {F : D.PELFlag b x ts} (p : D.CompositeSystem F) :
    D.CompositeDatum x ts := ⟨F.point (Fin.last ts.length), p (Fin.last ts.length)⟩

/-- The universal isogeny is selected from the explicitly supplied IsogenyQuotient
input. No existence principle beyond that named theorem input is used. -/
def Data.SphericalPELAlbaneseData.c46Isogeny (h : D.RealizesIsogenyQuotient) (t : Local.IntegralType s) : D.UniversalIsogeny t :=
  (h t).choose

/-- A composite system agrees with the actual correspondence kernels and
with composition of its algebraic isogenies and their Poincare duals. -/
def Data.SphericalPELAlbaneseData.IsCompositeSystem (h : D.RealizesIsogenyQuotient) (F : D.PELFlag b x ts)
    (p : D.CompositeSystem F) (f : D.StepSystem F) : Prop :=
  (p 0).isogeny.hom = eqToHom
    (congrArg (fun y => (D.fiberFamily b y).abelian.scheme) F.start.symm) ∧
  ∀ j : Fin ts.length,
    (p j.succ).isogeny.hom = (p j.castSucc).isogeny.hom ≫ (f j).isogeny.hom ∧
    (p j.succ).dualHom = (f j).dualHom ≫ (p j.castSucc).dualHom ∧
    ∀ v : Fin s,
      ((Subgroups.PointSubgroup.kernel (f j).isogeny.hom).inf
        (Subgroups.splitBlock (D.fiberFamily b (F.point j.castSucc))
          (D.localCharacter (v, false)) (ts.get j).multiplierNat)) =
      D.chosenKernelAtLift (ts.get j) (D.c46Isogeny h (ts.get j))
        (F.point j.castSucc) (F.branch j) (F.source j) v

/-- The actual chosen or opposite lattice of a composite, projected in a
single source frame. This uses the isogeny's rational Tate map. -/
def Data.SphericalPELAlbaneseData.compositeLattice (e : D.FiberFrame b x) {F : D.PELFlag b x ts}
    (p : D.CompositeSystem F) (j : Fin (ts.length + 1)) (v : Fin s × Bool) :
    Submodule ℤ_[q] (Fin 3 → ℚ_[q]) :=
  Rational.framedTateLattice e (p j).isogeny.hom v

/-- Realization of a linear flag by the same actual polarized, marked
composites as its geometric flag. Opposite lattices are compared by the
inverse cumulative multiplier, as required by inverse representatives. -/
def Data.SphericalPELAlbaneseData.RealizesLinearFlag (h : D.RealizesIsogenyQuotient) (e : D.FiberFrame b x)
    (B : Fin s → LinearMap.BilinForm ℚ_[q] (Fin 3 → ℚ_[q]))
    (L₀ : Fin s → Duality.RankThreeLattice ℤ_[q] ℚ_[q])
    (F : D.PELFlag b x ts) (L : Duality.LinearBlockFlags (q : ℤ_[q]) L₀ ts)
    (c : D.CompositeDatum x ts) : Prop :=
  ∃ (p : D.CompositeSystem F) (f : D.StepSystem F),
    D.IsCompositeSystem h F p f ∧ D.finalComposite p = c ∧
      ∀ (j : Fin (ts.length + 1)) (v : Fin s),
        D.compositeLattice e p j (v, false) = (L.val j v).val ∧
        D.compositeLattice e p j (v, true) =
          (HeckeKernel.qUnit q) ^ (-(Local.cumulativeMultiplier ts j)) •
            (B v).dualSubmodule (L.val j v).val

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison
