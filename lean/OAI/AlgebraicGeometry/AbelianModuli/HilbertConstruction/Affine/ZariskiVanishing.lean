import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.ZariskiDegreeOneVanishing
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SchemeIsomorphismCohomology
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.InjectiveSyzygySections

/-! # Zariski Vanishing -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.ZariskiVanishing.ZariskiCohomology

noncomputable section

universe u
open _root_.CategoryTheory Limits Opposite _root_.TopologicalSpace _root_.AlgebraicGeometry

/-- Genuine Ext-based cohomology of a quasicoherent module on an affine
spectrum is subsingleton in every positive degree. -/
theorem moduleSpecHSucc_subsingleton
    {R : CommRingCat.{u}} (M : (Spec R).Modules)
    [M.IsQuasicoherent] (n : ℕ) : Subsingleton (Zariski.Cohomology.ZariskiCohomology.H M (n + 1)) := by
  induction n using Nat.strong_induction_on generalizing R M with
  | h n ih =>
      cases n with
      | zero => exact ZariskiDegreeOneVanishing.ZariskiCohomology.moduleSpecHOne_subsingleton M
      | succ n =>
          refine subsingleton_of_forall_eq 0 fun c ↦ ?_
          let F := (SheafOfModules.toSheaf (Spec R).ringCatSheaf).obj M
          have hsyzygy : Open.InjectiveCokernelSequence.ZariskiCohomology.LocalKilling.AffineSyzygyAppSurjective F (n + 1) := by
            apply InjectiveSyzygySections.ZariskiCohomology.FlasqueAcyclicity.affineSyzygyAppSurjective_of_pullback_H_succ_subsingleton
            intro U hU k hk
            let : IsAffine (U : Scheme) := hU
            let N := (Scheme.Modules.restrictFunctor U.ι).obj M
            let : N.IsQuasicoherent := by
              dsimp [N]
              infer_instance
            let e := (U : Scheme).isoSpec
            let P := (Scheme.Modules.pushforward e.hom).obj N
            let : P.IsQuasicoherent := Quasicoherent.Image.quasiCompact_separated_directImage_quasicoherent e.hom _
            have hP : Subsingleton (Zariski.Cohomology.ZariskiCohomology.H P (k + 1)) := ih k hk P
            let : Subsingleton (Zariski.Cohomology.ZariskiCohomology.H P (k + 1)) := hP
            let : Subsingleton (CategoryTheory.Sheaf.H
                ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} e.hom.base).obj
                  ((SheafOfModules.toSheaf (U : Scheme).ringCatSheaf).obj N))
                (k + 1)) := by
              change Subsingleton (Zariski.Cohomology.ZariskiCohomology.H P (k + 1))
              exact hP
            have hN : Subsingleton (Zariski.Cohomology.ZariskiCohomology.H N (k + 1)) :=
              SchemeIsomorphismCohomology.ZariskiCohomology.sheafH_subsingleton_of_iso e
                ((SheafOfModules.toSheaf
                  (U : Scheme).ringCatSheaf).obj N) (k + 1)
            change Subsingleton (Zariski.Cohomology.ZariskiCohomology.H N (k + 1))
            exact hN
          obtain ⟨I, U, hfinite, hcover, haffine, _, hkilled⟩ :=
            FiniteCohomologyKillingCover.ZariskiCohomology.LocalKilling.schemeHSucc_finiteAffineKillingCover_of_affine_syzygy_app_surjective
              M (n + 1) c hsyzygy
          let : Finite I := hfinite
          let (i : I) : IsAffine (U i) := haffine i
          let : (cokernel (CohomologyCoverModule.ZariskiCohomology.toAffineCoverModule M U)).IsQuasicoherent :=
            CohomologyCoverModule.ZariskiCohomology.affineCoverCokernel_isQuasicoherent M U
          let : Subsingleton
              (Zariski.Cohomology.ZariskiCohomology.H (cokernel (CohomologyCoverModule.ZariskiCohomology.toAffineCoverModule M U)) (n + 1)) :=
            ih n (Nat.lt_succ_self n) _
          apply Zariski.CohomologyDimensionShift.ZariskiCohomology.toAffineCoverModule_H_succ_injective_of_cokernel_subsingleton
            M U hcover (n + 1)
          rw [hkilled, map_zero]

/-- Every genuine Ext-based positive-degree class of a quasicoherent module
on an affine spectrum is zero. -/
theorem moduleSpecHSucc_eq_zero
    {R : CommRingCat.{u}} (M : (Spec R).Modules)
    [M.IsQuasicoherent] (n : ℕ) (c : Zariski.Cohomology.ZariskiCohomology.H M (n + 1)) : c = 0 := by
  let : Subsingleton (Zariski.Cohomology.ZariskiCohomology.H M (n + 1)) := moduleSpecHSucc_subsingleton M n
  exact Subsingleton.elim _ _

/-- Genuine Ext-based cohomology of a quasicoherent module on any affine
scheme is subsingleton in every positive degree. -/
theorem moduleAffineHSucc_subsingleton
    {X : Scheme.{u}} [IsAffine X] (M : X.Modules)
    [M.IsQuasicoherent] (n : ℕ) : Subsingleton (Zariski.Cohomology.ZariskiCohomology.H M (n + 1)) := by
  let e := X.isoSpec
  let N := (Scheme.Modules.pushforward e.hom).obj M
  let : N.IsQuasicoherent := Quasicoherent.Image.quasiCompact_separated_directImage_quasicoherent e.hom _
  have hN : Subsingleton (Zariski.Cohomology.ZariskiCohomology.H N (n + 1)) := moduleSpecHSucc_subsingleton N n
  let : Subsingleton (Zariski.Cohomology.ZariskiCohomology.H N (n + 1)) := hN
  let : Subsingleton (CategoryTheory.Sheaf.H
      ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} e.hom.base).obj
        ((SheafOfModules.toSheaf X.ringCatSheaf).obj M)) (n + 1)) := by
    change Subsingleton (Zariski.Cohomology.ZariskiCohomology.H N (n + 1))
    exact hN
  exact SchemeIsomorphismCohomology.ZariskiCohomology.sheafH_subsingleton_of_iso e
    ((SheafOfModules.toSheaf X.ringCatSheaf).obj M) (n + 1)

/-- Every genuine Ext-based positive-degree class of a quasicoherent module
on an affine scheme is zero. -/
theorem moduleAffineHSucc_eq_zero
    {X : Scheme.{u}} [IsAffine X] (M : X.Modules)
    [M.IsQuasicoherent] (n : ℕ) (c : Zariski.Cohomology.ZariskiCohomology.H M (n + 1)) : c = 0 := by
  let : Subsingleton (Zariski.Cohomology.ZariskiCohomology.H M (n + 1)) := moduleAffineHSucc_subsingleton M n
  exact Subsingleton.elim _ _

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.ZariskiVanishing.ZariskiCohomology
