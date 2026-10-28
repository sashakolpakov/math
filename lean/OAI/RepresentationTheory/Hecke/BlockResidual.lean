import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.RationalResidual
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.CoordinateDualHecke

/-! # Block Residual -/

namespace OAI.RepresentationTheory.Hecke.BlockResidual.SphericalActionIntrinsic

noncomputable section

/-! Separate the active factor from the actual rational finite splitting.
The remaining factor is a homomorphism and commutes with the active lift.
These are group identities derived from the constructed local coordinates.
-/

open scoped Classical _root_.Matrix
open OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.RationalResidual

section Blocks

variable {J G : Type*} [DecidableEq J] [Group G] (μ : J)

def inactiveBlocks : (J → G) →* (J → G) where
  toFun g i := if i = μ then 1 else g i
  map_one' := by ext i; simp
  map_mul' g h := by ext i; by_cases hi : i = μ <;> simp [hi]

theorem blocks_factorization (g : J → G) :
    inactiveBlocks μ g * Pi.mulSingle μ (g μ) = g := by
  ext i
  by_cases hi : i = μ <;> simp [inactiveBlocks, hi]

theorem inactiveBlocks_commute (g : J → G) (a : G) :
    Commute (inactiveBlocks μ g) (Pi.mulSingle μ a) := by
  apply funext
  intro i
  by_cases hi : i = μ <;> simp [inactiveBlocks, hi]

end Blocks

section Local

variable (q : ℕ) [Fact q.Prime] {Place : Type} [Fintype Place] [DecidableEq Place]
  {n : ℕ} (c : (Place × Fin 3) ≃ Fin n) (μ : Place)
  {MpR MpF MpA : Type} [Group MpR] [Group MpF] [Group MpA]
  (W : Theta.PoissonAutomorphyNormalizationData.WeilData (Place × Fin 3) MpR MpF MpA)

theorem blockFamilyGL_single (g : Theta.Geometric.SphericalGU.Spherical.SL3 q) :
    AlgebraicGeometry.HodgeConjecture.CMExtraction.BlockFamilyMatrices.Local.blockFamilyGL c (Pi.mulSingle μ g) = AlgebraicGeometry.HodgeConjecture.CMExtraction.ActiveBlockMatrices.Local.activeBlockGL c μ g := by
  apply Units.ext
  have hb : (fun τ : Place => ((Pi.mulSingle μ g : Place → Theta.Geometric.SphericalGU.Spherical.SL3 q) τ).val) =
      (fun τ => if τ = μ then g.val else (1 : Matrix (Fin 3) (Fin 3) ℚ_[q])) := by
    funext τ
    by_cases h : τ = μ
    · subst τ
      simp
    · simp [h]
  exact congrArg (fun f => Matrix.reindex ((Equiv.prodComm (Fin 3) Place).trans c)
    ((Equiv.prodComm (Fin 3) Place).trans c) (Matrix.blockDiagonal f)) hb

theorem blockFamilyFiniteLift_single (g : Theta.Geometric.SphericalGU.Spherical.SL3 q) :
    AlgebraicGeometry.HodgeConjecture.CMExtraction.BlockFamilyLift.Local.blockFamilyFiniteLift q c W (Pi.mulSingle μ g) = AlgebraicGeometry.HodgeConjecture.CMExtraction.ActiveLocalLift.activeFiniteLift q c μ W g := by
  have h := AlgebraicGeometry.HodgeConjecture.CMExtraction.Finite.Sl.Local.finite_sl3_lift_unique q W
    ((AlgebraicGeometry.HodgeConjecture.CMExtraction.BlockFamilyLift.Local.blockFamilyFiniteLift q c W).comp
      (MonoidHom.mulSingle (fun _ : Place => Theta.Geometric.SphericalGU.Spherical.SL3 q) μ))
    (AlgebraicGeometry.HodgeConjecture.CMExtraction.ActiveLocalLift.activeFiniteLift q c μ W) (by
      intro a
      change W.finite.project (AlgebraicGeometry.HodgeConjecture.CMExtraction.BlockFamilyLift.Local.blockFamilyFiniteLift q c W (Pi.mulSingle μ a)) = _
      rw [AlgebraicGeometry.HodgeConjecture.CMExtraction.BlockFamilyLift.Local.blockFamilyFiniteLift_projection, AlgebraicGeometry.HodgeConjecture.CMExtraction.ActiveLocalLift.activeFiniteLift_projection, blockFamilyGL_single])
  exact DFunLike.congr_fun h g

end Local

attribute [local instance] AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.Multiplicity.nativePlaceDecidableEq AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.Multiplicity.nativeTripleDecidableEq

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E] [IsGalois ℚ E]
  {K : Type} [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  {Ga MpR MpF MpA : Type} [Group Ga] [TopologicalSpace Ga]
  [Group MpR] [Group MpF] [Group MpA]
  (D : Theta.Geometric.Data.ActiveHeckeThetaData E K s q (Fin s × Fin 3) Ga MpR MpF MpA)
  (hg : D.pel.HasIntegralModelGeometry) (hμ : D.pel.reference.μ = E.val.toRingHom)
  (v : AlgebraicGeometry.HodgeConjecture.CMExtraction.Multiplicity.Odd.Sign E) (hv : v.val 1 = true)
  (e : (Fin 3 → E) ≃ₗ[ℚ] (Sum (Fin s × Fin 3) (Fin s × Fin 3) → ℚ))
  (he : ∀ x y, RadialDilation.FramePositivity.Realization.coordinatePairing (e x) (e y) =
    Algebra.trace ℚ E (D.pel.reference.imaginaryScalar * AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.Multiplicity.nativeTensorPairing E D.pel.reference v x y))
  {n : ℕ} (c : (Fin s × Fin 3) ≃ Fin n) (u : MpF)
  (hu : AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.FiniteDilation.NativeFiniteCoordinateIdentity E D e u)

def activeRationalLift : D.RationalSU →* MpF :=
  (AlgebraicGeometry.HodgeConjecture.CMExtraction.ActiveLocalLift.activeFiniteLift q c D.pel.reference.distinguished D.weil).comp
    ((Pi.evalMonoidHom (fun _ : Fin s => Theta.Geometric.SphericalGU.Spherical.SL3 q) D.pel.reference.distinguished).comp
      (AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.RationalResidual.nativeLocalDualBlocks E D))

theorem active_residual_formula (g : D.RationalSU) :
    AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.RationalResidual.nativeConjugatedRationalSplitting E D hg hμ v hv e he u g *
        (activeRationalLift E D c g)⁻¹ =
      AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.RationalResidual.nativeRationalAwayResidual E D hg hμ v hv e he c u hu g *
        AlgebraicGeometry.HodgeConjecture.CMExtraction.BlockFamilyLift.Local.blockFamilyFiniteLift q c D.weil
          (inactiveBlocks D.pel.reference.distinguished (AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.RationalResidual.nativeLocalDualBlocks E D g)) := by
  rw [← AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.RationalResidual.nativeRationalAwayResidual_factorization E D hg hμ v hv e he c u hu g]
  have hb := congrArg (AlgebraicGeometry.HodgeConjecture.CMExtraction.BlockFamilyLift.Local.blockFamilyFiniteLift q c D.weil)
    (blocks_factorization D.pel.reference.distinguished (AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.RationalResidual.nativeLocalDualBlocks E D g))
  rw [map_mul, blockFamilyFiniteLift_single] at hb
  rw [← hb]
  change (_ * (_ * activeRationalLift E D c g)) * (activeRationalLift E D c g)⁻¹ = _
  group

include hu in
theorem active_residual_commute (g : D.RationalSU) (a : Theta.Geometric.SphericalGU.Spherical.SL3 q) :
    Commute
      (AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.RationalResidual.nativeConjugatedRationalSplitting E D hg hμ v hv e he u g *
        (activeRationalLift E D c g)⁻¹)
      (AlgebraicGeometry.HodgeConjecture.CMExtraction.ActiveLocalLift.activeFiniteLift q c D.pel.reference.distinguished D.weil a) := by
  rw [active_residual_formula E D hg hμ v hv e he c u hu g]
  apply Commute.mul_left
  · rw [← blockFamilyFiniteLift_single]
    exact AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.RationalResidual.nativeRationalAwayResidual_commute E D hg hμ v hv e he c u hu g _
  · have h := (inactiveBlocks_commute D.pel.reference.distinguished
      (AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.RationalResidual.nativeLocalDualBlocks E D g) a).map (AlgebraicGeometry.HodgeConjecture.CMExtraction.BlockFamilyLift.Local.blockFamilyFiniteLift q c D.weil)
    rwa [blockFamilyFiniteLift_single] at h

def activeResidualConjugated : D.RationalSU →* MpF :=
  AlgebraicGeometry.HodgeConjecture.CMExtraction.Finite.Sl.Local.commutingResidualHom
    (AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.RationalResidual.nativeConjugatedRationalSplitting E D hg hμ v hv e he u)
    (activeRationalLift E D c)
    (fun g h => active_residual_commute E D hg hμ v hv e he c u hu g
      (AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.RationalResidual.nativeLocalDualBlocks E D h D.pel.reference.distinguished))

def activeResidual : D.RationalSU →* MpF :=
  (MulAut.conj u⁻¹).toMonoidHom.comp (activeResidualConjugated E D hg hμ v hv e he c u hu)

theorem activeResidual_commute (g : D.RationalSU) (a : Theta.Geometric.SphericalGU.Spherical.SL3 q) :
    Commute (activeResidual E D hg hμ v hv e he c u hu g)
      (AlgebraicGeometry.HodgeConjecture.CMExtraction.CoordinateDualHecke.Local.coordinateDualLift q c D.pel.reference.distinguished D.weil u a) := by
  exact (active_residual_commute E D hg hμ v hv e he c u hu g
    (AlgebraicGeometry.HodgeConjecture.CMExtraction.Contragredient.Local.contragredient ℚ_[q] a)).map (MulAut.conj u⁻¹).toMonoidHom

end

end OAI.RepresentationTheory.Hecke.BlockResidual.SphericalActionIntrinsic
