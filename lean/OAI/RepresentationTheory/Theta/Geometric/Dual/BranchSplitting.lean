import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.BranchSplitting
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.BranchBaseChange
import OAI.RepresentationTheory.Theta.Geometric.Dual.NumberLifts
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.PeriodJetDifferentials
import OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.SmoothLocal
import Mathlib.AlgebraicGeometry.Sites.EtalePoint

/-! # Branch Splitting -/

namespace OAI.RepresentationTheory.Theta.Geometric.Dual.BranchSplitting

noncomputable section

/-! Every actual dual-number test has a full splitting of the finite
étale correspondence. The splitting is obtained by lifting a geometric
point into an étale splitting neighborhood through the square-zero extension. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem exists_dualBranchSplitting {X : Over OAI.AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} (C : OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Correspondences.EtaleCorrespondence X)
    (t : OAI.AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants.affineComplexTest OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.PeriodJet.dualTest ⟶ X) :
    ∃ n : ℕ, Nonempty (C.BranchSplitting t n) := by
  let r : CommRingCat.of (DualNumber ℂ) ⟶ CommRingCat.of ℂ :=
    CommRingCat.ofHom (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom
  let a := Spec.map r ≫ t.left
  obtain ⟨T, u, hu, hz, n, ⟨e⟩⟩ := C.exists_branch_splitting_at (a default)
  let : Etale u := hu
  obtain ⟨z, hz⟩ := hz
  obtain ⟨aU, haU, _⟩ := Scheme.exists_fac_of_etale_of_isSepClosed u a z hz
  obtain ⟨l, _, hlu⟩ := OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.SmoothLocal.SmoothLocalLifting.exists_scheme_lift u r
    (fun c => ⟨(c, 0), rfl⟩) (NumberLifts.dualNumberIdeal_square ℂ) aU t.left haU
  let v : OAI.AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants.affineComplexTest OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.PeriodJet.dualTest ⟶ Over.mk (u ≫ X.hom) :=
    Over.homMk l (by
      change l ≫ u ≫ X.hom = _
      rw [← Category.assoc, hlu]
      exact t.w)
  have hv : v ≫ (Over.homMk u rfl : Over.mk (u ≫ X.hom) ⟶ X) = t :=
    Over.OverMorphism.ext hlu
  exact ⟨n, hv ▸ ⟨C.pullbackBranchSplitting _ v e⟩⟩

theorem dualBranchTrace {X : Over OAI.AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} (C : OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Correspondences.EtaleCorrespondence X)
    (form other : OAI.AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants.OneForms X) (htrace : OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Branches.IsBranchTrace C form other)
    (t : OAI.AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants.affineComplexTest OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.PeriodJet.dualTest ⟶ X) (n : ℕ) (e : C.BranchSplitting t n) :
    OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.PeriodJetDifferentials.dualDifferential (other.val OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.PeriodJet.dualTest t) =
      ∑ i : Fin n, OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.PeriodJetDifferentials.dualDifferential
        (form.val OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.PeriodJet.dualTest (C.endpoint (C.splitBranch t e i))) := by
  rw [htrace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.PeriodJet.dualTest t n e, map_sum]

end

end OAI.RepresentationTheory.Theta.Geometric.Dual.BranchSplitting
