import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Residue.UnitCycleLifting
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.AffineCoverModel
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.CechModelBaseChange

/-! # Structure Model -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian

noncomputable section

/-! A finite projective model of the actual abelian structure sheaf has
surjective specialization on degree-zero cycles over a local base. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.AlgebraicGeometry.Scheme.Modules
open scoped TensorProduct

universe u

variable {S : Scheme.{u}} [IsAffine S] [IsNoetherianRing Γ(S, ⊤)] [IsLocalRing Γ(S, ⊤)]
variable {g : ℕ} (A : Schemes.AbelianScheme g S) [A.scheme.left.IsSeparated]
variable (P : HilbertConstruction.Projective.ProjectivePresentations.ProjectivePresentation A.scheme)
variable {ι : Type u} [LinearOrder ι] [Finite ι] (U : ι → A.scheme.left.Opens)
variable (hU : iSup U = ⊤) (ha : ∀ i, IsAffineOpen (U i))

include P hU ha

theorem Schemes.AbelianScheme.exists_structureModel :
    ∃ (D : CochainComplex (ModuleCat.{u} Γ(S, ⊤)) ℕ)
      (φ : D ⟶ SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.orderedBaseCechComplex A.scheme.hom (SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj A.scheme.left) U),
      QuasiIso φ ∧
      (∀ q, Module.Finite Γ(S, ⊤) (D.X q)) ∧
      (∀ q, Module.Projective Γ(S, ⊤) (D.X q)) ∧
      (∀ z : IsLocalRing.ResidueField Γ(S, ⊤) ⊗[Γ(S, ⊤)] D.X 0,
        (D.d 0 1).hom.baseChange (IsLocalRing.ResidueField Γ(S, ⊤)) z = 0 →
        ∃ x : D.X 0, D.d 0 1 x = 0 ∧
          (1 : IsLocalRing.ResidueField Γ(S, ⊤)) ⊗ₜ[Γ(S, ⊤)] x = z) := by
  obtain ⟨D, φ, hq, _, hfin, hproj, hφ⟩ :=
    Quotients.FiniteDescent.AffineCoverModel.Construction.AffineCoverPerfectModel.exists_model A.scheme.hom P U hU ha (Line.Bundles.LineBundle.trivial A.scheme.left)
  change D ⟶ SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.orderedBaseCechComplex A.scheme.hom (SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj A.scheme.left) U at φ
  have : QuasiIso φ := hq
  let q := ReferenceFamily.Affine.CoefficientUnitExactness.coefficientFieldPoint S (IsLocalRing.ResidueField Γ(S, ⊤))
  have : (SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj A.scheme.left).IsQuasicoherent :=
    Quotients.FiniteDescent.LineBundleFree.Construction.LineBundleCoherence.quasicoherent (Line.Bundles.LineBundle.trivial A.scheme.left)
  have : QuasiIso (Quotients.FiniteDescent.CechModelBaseChange.Construction.CechBaseChangeMap.modelMap (pullback.fst A.scheme.hom q) A.scheme.hom
      (pullback.snd A.scheme.hom q) q pullback.condition (SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj A.scheme.left) U φ) :=
    Quotients.FiniteDescent.CechModelBaseChange.Construction.CechBaseChangeMap.modelMap_quasiIso (pullback.fst A.scheme.hom q) A.scheme.hom
      (pullback.snd A.scheme.hom q) q (SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj A.scheme.left) U φ
      (IsPullback.of_hasPullback A.scheme.hom q)
      (fun n i => SheafCohomology.Cech.Cochains.IsAffineOpen.cechIntersection U ha n i.1) hφ
  exact ⟨D, φ, hq, hfin, hproj, A.structureModel_residue_cycle_lift U hU φ⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian
