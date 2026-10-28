import OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineFrame.PrincipalCovers
import OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallinePrincipal.Factorization
import OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.ThickeningTopology

/-! # Cover Lifting -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineFrame.CoverLifting.CrystallineFrameCoverLifting

noncomputable section

/-!
# Lifting principal covers through the native frame extension

A principal cover of a frame extension pulls back, under its objectwise
augmentation, to a principal cover of the original crystalline object.
After applying the native frame functor, every resulting arrow factors
through the corresponding member of the given cover. Only the reduction
of the augmentation is used; no natural augmentation is asserted.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable (p : ℕ) [Fact p.Prime] (k B σ : Type u) [Field k] [CharP k p]
  [CommRing B] [Algebra k B] (a : σ → B)
  (Q : Site.Object p k (AffineFrameCover.CrystallineAffineFrameCover.affineScheme k B))

local notation "X" => OAI.AlgebraicGeometry.Crystalline.Cohomology.AffineFrameCover.CrystallineAffineFrameCover.affineScheme k B
local notation "F" => OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineFrame.Functor.CrystallineFrameFunctor.functor p k B σ a
local notation "G" => DividedPowerAlgebra Q.thickening.ring (σ →₀ Q.thickening.ring)

def coefficient (t : ((F).obj Q).thickening.ring) : Q.thickening.ring :=
  Multivariable.Reduction.MultivariableReduction.augmentation Q.thickening.ring σ t

theorem coefficient_span (ι : Type u) (t : ι → ((F).obj Q).thickening.ring)
    (ht : Ideal.span (Set.range t) = ⊤) :
    Ideal.span (Set.range (fun i => coefficient p k B σ a Q (t i))) = ⊤ := by
  let ε : G →+* Q.thickening.ring :=
    (Multivariable.Reduction.MultivariableReduction.augmentation Q.thickening.ring σ).toRingHom
  have h : Ideal.span (ε '' Set.range (fun i => (t i : G))) = ⊤ :=
    (Ideal.map_span ε _).symm.trans
      ((congrArg (Ideal.map ε) ht).trans (Ideal.map_top ε))
  exact (congrArg Ideal.span (Set.range_comp' ε (fun i => (t i : G)))).trans h

theorem mapped_unit (t : ((F).obj Q).thickening.ring) :
    IsUnit ((PrincipalCovers.CrystallineFramePrincipalCovers.map p k B σ a Q
      (coefficient p k B σ a Q t)).ambientMap t) := by
  let s := coefficient p k B σ a Q t
  let P := (F).obj (CrystallinePrincipal.Opens.CrystallinePrincipalOpens.object p k X Q s)
  let f := PrincipalCovers.CrystallineFramePrincipalCovers.map p k B σ a Q s
  apply PD.ThickeningTopology.PDThickeningTopology.isUnit_of_reduction p k P.residueRing P.thickening
  rw [f.reduction_comm]
  change IsUnit (algebraMap Q.residueRing (Localization.Away (Q.thickening.reduction s))
    (Q.thickening.reduction s))
  exact IsLocalization.Away.algebraMap_isUnit (Q.thickening.reduction s)

def factor (t : ((F).obj Q).thickening.ring) :
    (F).obj (CrystallinePrincipal.Opens.CrystallinePrincipalOpens.object p k X Q (coefficient p k B σ a Q t)) ⟶
      CrystallinePrincipal.Opens.CrystallinePrincipalOpens.object p k X ((F).obj Q) t :=
  CrystallinePrincipal.Factorization.CrystallinePrincipalFactorization.lift p k X
    (PrincipalCovers.CrystallineFramePrincipalCovers.map p k B σ a Q (coefficient p k B σ a Q t)) t
    (mapped_unit p k B σ a Q t)

theorem factor_projection (t : ((F).obj Q).thickening.ring) :
    factor p k B σ a Q t ≫ CrystallinePrincipal.Opens.CrystallinePrincipalOpens.projection p k X ((F).obj Q) t =
      (F).map (CrystallinePrincipal.Opens.CrystallinePrincipalOpens.projection p k X Q (coefficient p k B σ a Q t)) :=
  CrystallinePrincipal.Factorization.CrystallinePrincipalFactorization.lift_projection p k X _ _ _

theorem lifted_covering_mem (ι : Type u) (t : ι → ((F).obj Q).thickening.ring)
    (ht : Ideal.span (Set.range t) = ⊤) :
    Sieve.generate (CrystallinePrincipal.Covers.CrystallinePrincipalCovers.presieve p k X Q ι
      (fun i => coefficient p k B σ a Q (t i))) ∈ Site.topology p k X Q :=
  CrystallinePrincipal.Covers.CrystallinePrincipalCovers.covering_mem p k X Q ι _
    (coefficient_span p k B σ a Q ι t ht)

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineFrame.CoverLifting.CrystallineFrameCoverLifting
