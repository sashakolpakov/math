import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.CM.PointsProjectorSum
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Kernel.FamilyTransport

/-! # Projector Levels -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ProjectorLevels

noncomputable section

/-! Integral lifts of the same coefficient idempotent at different
q-power levels induce the same lower-torsion action. The resulting block
isomorphism preserves the original inclusion in the abelian scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.CM.PointsProjectorSum.Construction

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [Field K] [NumberField K] {κ : K →+* ℂ} {q : ℕ} [Fact q.Prime]
variable (j : PELModuli.CMPoints.Arithmetic.QadicChoice K κ q) (iota : E →+* K) (hsplit : j.HasSplitCoordinates iota)

local instance : DecidableEq Gal(E/ℚ) := Classical.decEq _

theorem projector_lower_coordinates {m n : ℕ} (hmn : m ≤ n) (τ : Gal(E/ℚ)) :
    j.residueCoordinates iota m (j.projector iota hsplit n τ) = Pi.single τ 1 := by
  classical
  ext υ
  have h := RingHom.congr_fun (j.residueCharacter_compatible iota υ m n hmn)
    (j.projector iota hsplit n τ)
  change (ZMod.castHom (pow_dvd_pow q hmn) (ZMod (q ^ m)))
    (j.residueCharacter iota υ n (j.projector iota hsplit n τ)) =
      j.residueCharacter iota υ m (j.projector iota hsplit n τ) at h
  change j.residueCharacter iota υ m (j.projector iota hsplit n τ) = _
  rw [← h]
  have hc := congrFun (j.projector_coordinates iota hsplit n τ) υ
  change j.residueCharacter iota υ n (j.projector iota hsplit n τ) = _ at hc
  rw [hc]
  by_cases hv : υ = τ
  · subst υ
    simp only [Pi.single_eq_same]
    exact map_one (ZMod.castHom (pow_dvd_pow q hmn) (ZMod (q ^ m)))
  · simp [hv]

theorem projector_level_congruence {m n : ℕ} (hmn : m ≤ n) (τ : Gal(E/ℚ)) :
    j.projector iota hsplit n τ - j.projector iota hsplit m τ ∈
      Ideal.span ({(q ^ m : NumberField.RingOfIntegers E)} : Set (NumberField.RingOfIntegers E)) := by
  rw [← (hsplit m).2]
  change j.residueCoordinates iota m
    (j.projector iota hsplit n τ - j.projector iota hsplit m τ) = 0
  rw [map_sub, projector_lower_coordinates j iota hsplit hmn,
    j.projector_coordinates, sub_self]

variable {S : Scheme} {d : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme d S)
variable (σ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A)

theorem native_projector_change_level {m n : ℕ} (hmn : m ≤ n) (τ : Gal(E/ℚ)) :
    AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionMap (q ^ m) (σ.map (j.projector iota hsplit n τ)) =
      AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionMap (q ^ m) (σ.map (j.projector iota hsplit m τ)) := by
  apply (cancel_mono (AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionInclusion A.scheme (q ^ m))).mp
  rw [AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionMap_inclusion, AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionMap_inclusion]
  exact PELModuli.CMPoints.BlocksProjectors.action_eq_of_congruence A σ _ _ (q ^ m)
    (by simpa only [Nat.cast_pow] using projector_level_congruence j iota hsplit hmn τ)
    _ (AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionInclusion A.scheme (q ^ m)) (AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionInclusion_killed A.scheme (q ^ m))

section Fixed

variable {T : Over S} [GrpObj T] [IsCommMonObj T]
variable (p r : T ⟶ T) [IsMonHom p] [IsMonHom r]

def fixedPointIsoOfEq (h : p = r) : AbelianScheme.IsogenyQuotient.BlockGroups.Construction.fixedPointScheme p ≅ AbelianScheme.IsogenyQuotient.BlockGroups.Construction.fixedPointScheme r := by
  subst r
  exact Iso.refl _

omit [IsCommMonObj T] in
theorem fixedPointIsoOfEq_inclusion (h : p = r) :
    (fixedPointIsoOfEq p r h).hom ≫ AbelianScheme.IsogenyQuotient.BlockGroups.Construction.fixedPointInclusion r = AbelianScheme.IsogenyQuotient.BlockGroups.Construction.fixedPointInclusion p := by
  subst r
  exact Category.id_comp _

end Fixed

def nativeBlockLevelIso {m n : ℕ} (hmn : m ≤ n) (τ : Gal(E/ℚ)) :
    AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock (q ^ m) (σ.map (j.projector iota hsplit n τ)) ≅
      AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock (q ^ m) (σ.map (j.projector iota hsplit m τ)) :=
  fixedPointIsoOfEq _ _ (native_projector_change_level j iota hsplit A σ hmn τ)

theorem nativeBlockLevelIso_inclusion {m n : ℕ} (hmn : m ≤ n) (τ : Gal(E/ℚ)) :
    (nativeBlockLevelIso j iota hsplit A σ hmn τ).hom ≫
      AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion (q ^ m) (σ.map (j.projector iota hsplit m τ)) =
        AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion (q ^ m) (σ.map (j.projector iota hsplit n τ)) := by
  rw [AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion, ← Category.assoc, nativeBlockLevelIso,
    fixedPointIsoOfEq_inclusion]
  rfl

theorem nativeBlockLevel_family {m n : ℕ} (hmn : m ≤ n) (τ : Gal(E/ℚ)) {P : Over S} :
    Kernel.Base.fixedKernelFamily (P := P) (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion (q ^ m) (σ.map (j.projector iota hsplit n τ))) =
      Kernel.Base.fixedKernelFamily (P := P) (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion (q ^ m) (σ.map (j.projector iota hsplit m τ))) :=
  Kernel.FamilyTransport.Family.fixed_iso _ _ (nativeBlockLevelIso j iota hsplit A σ hmn τ)
    (nativeBlockLevelIso_inclusion j iota hsplit A σ hmn τ)

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ProjectorLevels
