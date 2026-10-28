import OAI.RepresentationTheory.Theta.Geometric.SingletonBranchFibers

/-! # Branch Reduction -/

namespace OAI.RepresentationTheory.Theta.Geometric.Dual.BranchReduction

noncomputable section

section

/-! A finite étale branch over a dual-number test is determined by its
ordinary point. Reduction gives a bijection and retains every branch once. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

def branchRestriction {B : Scheme.{0}} {X : Over B} (C : AlgebraicGeometry.AbelianScheme.TateComparison.Correspondences.EtaleCorrespondence X)
    {T T' : Over B} (t : T ⟶ X) (a : T' ⟶ T) : C.Fiber t → C.Fiber (a ≫ t) :=
  fun b => ⟨a ≫ b.val, (Category.assoc _ _ _).trans (congrArg (a ≫ ·) b.property)⟩

theorem splitBranch_bijective_of_singleton {B : Scheme.{0}} {X : Over B} (C : AlgebraicGeometry.AbelianScheme.TateComparison.Correspondences.EtaleCorrespondence X)
    {T : Over B} [Unique T.left] (t : T ⟶ X) {n : ℕ} (e : C.BranchSplitting t n) :
    Function.Bijective (C.splitBranch t e) := by
  set_option backward.isDefEq.respectTransparency false in
    let F : Fin n ≃ C.Fiber ((𝟙 T) ≫ t) := SingletonBranchFibers.splitSingletonFiberEquiv C (T := T) (T' := T) t (𝟙 T) (n := n) e
    constructor
    · intro i j hij
      apply F.injective
      apply Subtype.ext
      simpa only [F, SingletonBranchFibers.splitSingletonFiberEquiv_val, Category.id_comp] using congrArg Subtype.val hij
    · intro b
      let b' : C.Fiber ((𝟙 T) ≫ t) := ⟨b.val, by simpa only [Category.id_comp] using b.property⟩
      obtain ⟨i, hi⟩ := F.surjective b'
      refine ⟨i, Subtype.ext ?_⟩
      simpa only [F, SingletonBranchFibers.splitSingletonFiberEquiv_val, Category.id_comp] using congrArg Subtype.val hi

theorem branchRestriction_bijective_of_singleton {B : Scheme.{0}} {X : Over B}
    (C : AlgebraicGeometry.AbelianScheme.TateComparison.Correspondences.EtaleCorrespondence X) {T T' : Over B} [Unique T.left] [Unique T'.left]
    (t : T ⟶ X) (a : T' ⟶ T) {n : ℕ} (e : C.BranchSplitting t n) :
    Function.Bijective (branchRestriction C t a) := by
  let F := Equiv.ofBijective (C.splitBranch t e) (splitBranch_bijective_of_singleton C t e)
  let G : Fin n ≃ C.Fiber (a ≫ t) := SingletonBranchFibers.splitSingletonFiberEquiv C (T := T) (T' := T') t a (n := n) e
  have h : branchRestriction C t a = G ∘ F.symm := by
    funext b
    obtain ⟨i, rfl⟩ := F.surjective b
    change branchRestriction C t a (F i) = G (F.symm (F i))
    rw [Equiv.symm_apply_apply]
    apply Subtype.ext
    exact (SingletonBranchFibers.splitSingletonFiberEquiv_val C t a e i).symm
  rw [h]
  exact G.bijective.comp F.symm.bijective

theorem dualBranchReduction_bijective {X : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} (C : AlgebraicGeometry.AbelianScheme.TateComparison.Correspondences.EtaleCorrespondence X)
    (t : AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants.affineComplexTest AlgebraicGeometry.HodgeConjecture.CMExtraction.PeriodJet.dualTest ⟶ X) :
    Function.Bijective (branchRestriction C t AlgebraicGeometry.HodgeConjecture.CMExtraction.PeriodJet.dualClosedPoint) := by
  let : Subsingleton (AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants.affineComplexTest AlgebraicGeometry.HodgeConjecture.CMExtraction.PeriodJet.dualTest).left :=
    inferInstanceAs (Subsingleton (PrimeSpectrum (DualNumber ℂ)))
  let : Unique (AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants.affineComplexTest AlgebraicGeometry.HodgeConjecture.CMExtraction.PeriodJet.dualTest).left :=
    ⟨⟨AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying AlgebraicGeometry.HodgeConjecture.CMExtraction.PeriodJet.dualClosedPoint⟩, fun _ => Subsingleton.elim _ _⟩
  let : Unique (Over.mk (𝟙 AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase)).left := inferInstanceAs (Unique AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase)
  obtain ⟨n, ⟨e⟩⟩ := Dual.BranchSplitting.exists_dualBranchSplitting C t
  exact branchRestriction_bijective_of_singleton C t AlgebraicGeometry.HodgeConjecture.CMExtraction.PeriodJet.dualClosedPoint e

end

/-! TateComparison's algebraic trace is the raw sum over the ordinary source
fiber, each point carrying its unique lift of the prescribed derivative. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

def dualBranchLift {X : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} (C : AlgebraicGeometry.AbelianScheme.TateComparison.Correspondences.EtaleCorrespondence X)
    (t : AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants.affineComplexTest AlgebraicGeometry.HodgeConjecture.CMExtraction.PeriodJet.dualTest ⟶ X) :
    C.Fiber (AlgebraicGeometry.HodgeConjecture.CMExtraction.PeriodJet.dualClosedPoint ≫ t) → C.Fiber t :=
  (Equiv.ofBijective (branchRestriction C t AlgebraicGeometry.HodgeConjecture.CMExtraction.PeriodJet.dualClosedPoint)
    (dualBranchReduction_bijective C t)).symm

theorem dualBranchLift_reduction {X : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} (C : AlgebraicGeometry.AbelianScheme.TateComparison.Correspondences.EtaleCorrespondence X)
    (t : AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants.affineComplexTest AlgebraicGeometry.HodgeConjecture.CMExtraction.PeriodJet.dualTest ⟶ X)
    (b : C.Fiber (AlgebraicGeometry.HodgeConjecture.CMExtraction.PeriodJet.dualClosedPoint ≫ t)) :
    branchRestriction C t AlgebraicGeometry.HodgeConjecture.CMExtraction.PeriodJet.dualClosedPoint (dualBranchLift C t b) = b :=
  (Equiv.ofBijective (branchRestriction C t AlgebraicGeometry.HodgeConjecture.CMExtraction.PeriodJet.dualClosedPoint)
    (dualBranchReduction_bijective C t)).apply_symm_apply b

theorem dualBranchLift_split {X : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} (C : AlgebraicGeometry.AbelianScheme.TateComparison.Correspondences.EtaleCorrespondence X)
    (t : AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants.affineComplexTest AlgebraicGeometry.HodgeConjecture.CMExtraction.PeriodJet.dualTest ⟶ X)
    {n : ℕ} (e : C.BranchSplitting t n) (i : Fin n) :
    dualBranchLift C t (C.splitFiberEquiv t AlgebraicGeometry.HodgeConjecture.CMExtraction.PeriodJet.dualClosedPoint e i) = C.splitBranch t e i := by
  apply (dualBranchReduction_bijective C t).1
  rw [dualBranchLift_reduction]
  apply Subtype.ext
  exact C.splitFiberEquiv_val t AlgebraicGeometry.HodgeConjecture.CMExtraction.PeriodJet.dualClosedPoint e i

theorem dualBranchTrace_indexed {X : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} (C : AlgebraicGeometry.AbelianScheme.TateComparison.Correspondences.EtaleCorrespondence X)
    (form other : AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants.OneForms X) (htrace : AlgebraicGeometry.AbelianScheme.TateComparison.Branches.IsBranchTrace C form other)
    (t : AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants.affineComplexTest AlgebraicGeometry.HodgeConjecture.CMExtraction.PeriodJet.dualTest ⟶ X)
    (I : Type) [Fintype I] (β : I ≃ C.Fiber (AlgebraicGeometry.HodgeConjecture.CMExtraction.PeriodJet.dualClosedPoint ≫ t)) :
    AlgebraicGeometry.HodgeConjecture.CMExtraction.PeriodJetDifferentials.dualDifferential (other.val AlgebraicGeometry.HodgeConjecture.CMExtraction.PeriodJet.dualTest t) =
      ∑ i : I, AlgebraicGeometry.HodgeConjecture.CMExtraction.PeriodJetDifferentials.dualDifferential
        (form.val AlgebraicGeometry.HodgeConjecture.CMExtraction.PeriodJet.dualTest (C.endpoint (dualBranchLift C t (β i)))) := by
  let : Fintype (C.Fiber (AlgebraicGeometry.HodgeConjecture.CMExtraction.PeriodJet.dualClosedPoint ≫ t)) := Fintype.ofEquiv I β
  obtain ⟨n, ⟨e⟩⟩ := Dual.BranchSplitting.exists_dualBranchSplitting C t
  rw [Dual.BranchSplitting.dualBranchTrace C form other htrace t n e]
  let f := fun b : C.Fiber (AlgebraicGeometry.HodgeConjecture.CMExtraction.PeriodJet.dualClosedPoint ≫ t) =>
    AlgebraicGeometry.HodgeConjecture.CMExtraction.PeriodJetDifferentials.dualDifferential (form.val AlgebraicGeometry.HodgeConjecture.CMExtraction.PeriodJet.dualTest (C.endpoint (dualBranchLift C t b)))
  have hsum : (∑ i : Fin n, AlgebraicGeometry.HodgeConjecture.CMExtraction.PeriodJetDifferentials.dualDifferential
      (form.val AlgebraicGeometry.HodgeConjecture.CMExtraction.PeriodJet.dualTest (C.endpoint (C.splitBranch t e i)))) =
      ∑ i : Fin n, f (C.splitFiberEquiv t AlgebraicGeometry.HodgeConjecture.CMExtraction.PeriodJet.dualClosedPoint e i) := by
    apply Finset.sum_congr rfl
    intro i _
    change _ = AlgebraicGeometry.HodgeConjecture.CMExtraction.PeriodJetDifferentials.dualDifferential
      (form.val AlgebraicGeometry.HodgeConjecture.CMExtraction.PeriodJet.dualTest (C.endpoint (dualBranchLift C t
        (C.splitFiberEquiv t AlgebraicGeometry.HodgeConjecture.CMExtraction.PeriodJet.dualClosedPoint e i))))
    rw [dualBranchLift_split]
  exact hsum.trans (((C.splitFiberEquiv t AlgebraicGeometry.HodgeConjecture.CMExtraction.PeriodJet.dualClosedPoint e).sum_comp f).trans
    (β.sum_comp f).symm)

end

end OAI.RepresentationTheory.Theta.Geometric.Dual.BranchReduction
