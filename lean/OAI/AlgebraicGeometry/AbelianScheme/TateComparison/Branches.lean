import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants

/-! # Branches -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison

noncomputable section

/-! Actual local branch presentations of a correspondence and the
sum-of-pullbacks meaning of its trace on one-forms. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

section

variable {B B' : Scheme.{u}} {X : Over B} (C : Correspondences.EtaleCorrespondence X)

/-- A correspondence remains finite etale over its source after base change. -/
abbrev Correspondences.EtaleCorrespondence.baseChange (f : B' ⟶ B) : Correspondences.EtaleCorrespondence ((Over.pullback f).obj X) where
  cover := (Over.pullback f).obj C.cover
  source := (Over.pullback f).map C.source
  target := (Over.pullback f).map C.target
  finite := MorphismProperty.overPullbackMap f C.source C.finite
  etale := MorphismProperty.overPullbackMap f C.source C.etale

variable {T : Over B} (x : T ⟶ X)

/-- A section of the scheme-theoretic source fiber gives its actual branch. -/
def Correspondences.EtaleCorrespondence.branchOfSection
    (a : T.left ⟶ pullback C.source.left x.left)
    (ha : a ≫ pullback.snd C.source.left x.left = 𝟙 _) : C.Fiber x :=
  ⟨Over.homMk (a ≫ pullback.fst C.source.left x.left) (by
    calc
      _ = a ≫ pullback.fst C.source.left x.left ≫ C.source.left ≫ X.hom := by
        rw [C.source.w]
        simp only [Category.assoc]
      _ = a ≫ pullback.snd C.source.left x.left ≫ x.left ≫ X.hom := by
        rw [← Category.assoc (pullback.fst C.source.left x.left), pullback.condition]
        simp only [Category.assoc]
      _ = T.hom := by rw [← Category.assoc a, ha, Category.id_comp, x.w]), by
    apply Over.OverMorphism.ext
    change (a ≫ pullback.fst C.source.left x.left) ≫ C.source.left = x.left
    rw [Category.assoc, pullback.condition, ← Category.assoc, ha, Category.id_comp]⟩

/-- A splitting is an isomorphism of schemes over the test scheme, from
n disjoint copies of that scheme to the pulled-back source cover. -/
abbrev Correspondences.EtaleCorrespondence.BranchSplitting (n : ℕ) :=
  (∐ fun _ : Fin n => Over.mk (𝟙 T.left)) ≅
    Over.mk (pullback.snd C.source.left x.left)

/-- The branches are constructed from the splitting's component inclusions. -/
def Correspondences.EtaleCorrespondence.splitBranch {n : ℕ} (e : C.BranchSplitting x n) (i : Fin n) : C.Fiber x :=
  C.branchOfSection x (Sigma.ι (fun _ : Fin n => Over.mk (𝟙 T.left)) i ≫ e.hom).left
    (Sigma.ι (fun _ : Fin n => Over.mk (𝟙 T.left)) i ≫ e.hom).w

end

/-- The trace identity is stated on every actual affine branch splitting.
It is the sum of pullbacks by the target branches, with multiplicities.
No independently supplied linear operator is used to define this relation. -/
def Branches.IsBranchTrace {X : Over Foundations.Scheme.ProjectiveSpace.complexBase} (C : Correspondences.EtaleCorrespondence X)
    (ω η : FormConstants.OneForms X) : Prop :=
  ∀ (R : CommAlgCat.{0} ℂ) (x : FormConstants.affineComplexTest R ⟶ X) (n : ℕ)
    (e : C.BranchSplitting x n),
    η.val R x = ∑ i : Fin n, ω.val R (C.endpoint (C.splitBranch x e i))

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison
