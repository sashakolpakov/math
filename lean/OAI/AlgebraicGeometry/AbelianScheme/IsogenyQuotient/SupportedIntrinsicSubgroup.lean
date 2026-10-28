import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.IdentitySubgroup
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Torsion.Groups
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.SubgroupTransport
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.OppositeKernel

/-! # Supported Intrinsic Subgroup -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.SupportedIntrinsicSubgroup.Construction

noncomputable section

/-!
The original supported subgroup model gives a native subgroup inclusion
into its actual torsion block. Its image is exactly the original relative
subgroup pulled back along the block inclusion.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u v

theorem isMonHom_of_mono_factorization {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]
    {G H K : C} [GrpObj G] [GrpObj H] [GrpObj K]
    (f : G ⟶ H) (i : H ⟶ K) [IsMonHom i] [Mono i]
    (g : G ⟶ K) [IsMonHom g] (h : f ≫ i = g) : IsMonHom f := by
  apply GroupMaps.Construction.isMonHom_of_pointwise
  · intro T
    apply (cancel_mono i).mp
    rw [Category.assoc, h, MonObj.one_comp, MonObj.one_comp]
  · intro T x y
    apply (cancel_mono i).mp
    rw [Category.assoc, h, MonObj.mul_comp, MonObj.mul_comp,
      Category.assoc, Category.assoc, h]

variable {S : Scheme.{u}} {d : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme d S)
  (F : TorsionQuotient.SubgroupFunctor.RelativeSubgroup A.scheme (Over.mk (𝟙 S))) (R : F.Model)
  (n : ℕ) (p : A.scheme ⟶ A.scheme) [IsMonHom p]
  (hkilled : F.KilledBy n) (hsupport : SubgroupFunctor.Construction.SupportedOn F p)

include hkilled in
theorem identitySubgroupInclusion_killed : (IdentitySubgroup.Construction.identitySubgroupInclusion A F R) ^ n = 1 := by
  rw [IdentitySubgroup.Construction.identitySubgroupInclusion_model, ← MonObj.comp_pow,
    R.toGroup_pow_eq_one hkilled, MonObj.comp_one]

omit [IsMonHom p] in
include hsupport in
theorem identitySubgroupInclusion_supported :
    IdentitySubgroup.Construction.identitySubgroupInclusion A F R ≫ p = IdentitySubgroup.Construction.identitySubgroupInclusion A F R := by
  rw [IdentitySubgroup.Construction.identitySubgroupInclusion_model, Category.assoc,
    (SubgroupFunctor.Construction.supportedOn_iff_model_equation F R p).mp hsupport]

def supportedNativeSubgroupInclusion : (Subgroup.Construction.subgroupGroupScheme F R).X ⟶ OppositeKernel.Construction.torsionBlock n p :=
  OppositeKernel.Construction.torsionBlockLift n p (IdentitySubgroup.Construction.identitySubgroupInclusion A F R)
    (identitySubgroupInclusion_killed A F R n hkilled)
    (identitySubgroupInclusion_supported A F R p hsupport)

theorem supportedNativeSubgroupInclusion_comp :
    supportedNativeSubgroupInclusion A F R n p hkilled hsupport ≫ OppositeKernel.Construction.torsionBlockInclusion n p =
      IdentitySubgroup.Construction.identitySubgroupInclusion A F R :=
  OppositeKernel.Construction.torsionBlockLift_inclusion n p (IdentitySubgroup.Construction.identitySubgroupInclusion A F R)
    (identitySubgroupInclusion_killed A F R n hkilled)
    (identitySubgroupInclusion_supported A F R p hsupport)

instance supportedNativeSubgroupInclusion_isMonHom :
    IsMonHom (supportedNativeSubgroupInclusion A F R n p hkilled hsupport) := by
  exact @isMonHom_of_mono_factorization (Over S) _ _
    (Subgroup.Construction.subgroupGroupScheme F R).X (OppositeKernel.Construction.torsionBlock n p) A.scheme
    (Subgroup.Construction.subgroupGroupScheme F R).grp (inferInstanceAs (GrpObj (OppositeKernel.Construction.torsionBlock n p))) A.group
    (supportedNativeSubgroupInclusion A F R n p hkilled hsupport) (OppositeKernel.Construction.torsionBlockInclusion n p)
    (inferInstanceAs (IsMonHom (OppositeKernel.Construction.torsionBlockInclusion n p)))
    (inferInstanceAs (Mono (OppositeKernel.Construction.torsionBlockInclusion n p)))
    (IdentitySubgroup.Construction.identitySubgroupInclusion A F R) (IdentitySubgroup.Construction.identitySubgroupInclusion_isMonHom A F R)
    (supportedNativeSubgroupInclusion_comp A F R n p hkilled hsupport)

instance supportedNativeSubgroupInclusion_mono :
    Mono (supportedNativeSubgroupInclusion A F R n p hkilled hsupport) := by
  have : IsClosedImmersion (IdentitySubgroup.Construction.identitySubgroupInclusion A F R).left :=
    IdentitySubgroup.Construction.identitySubgroupInclusion_closedImmersion A F R
  have : Mono (IdentitySubgroup.Construction.identitySubgroupInclusion A F R) := Over.mono_of_mono_left _
  have : Mono (supportedNativeSubgroupInclusion A F R n p hkilled hsupport ≫ OppositeKernel.Construction.torsionBlockInclusion n p) :=
    (supportedNativeSubgroupInclusion_comp A F R n p hkilled hsupport).symm ▸ inferInstance
  exact mono_of_mono (supportedNativeSubgroupInclusion A F R n p hkilled hsupport) (OppositeKernel.Construction.torsionBlockInclusion n p)

theorem supportedNativeSubgroupInclusion_points
    (T : Over S) (t : T ⟶ Over.mk (𝟙 S)) (y : T ⟶ OppositeKernel.Construction.torsionBlock n p) :
    (∃ z : T ⟶ (Subgroup.Construction.subgroupGroupScheme F R).X,
      z ≫ supportedNativeSubgroupInclusion A F R n p hkilled hsupport = y) ↔
      y ≫ OppositeKernel.Construction.torsionBlockInclusion n p ∈ F.points T t := by
  have : IsClosedImmersion (IdentitySubgroup.Construction.identitySubgroupInclusion A F R).left :=
    IdentitySubgroup.Construction.identitySubgroupInclusion_closedImmersion A F R
  have : Mono (IdentitySubgroup.Construction.identitySubgroupInclusion A F R) := Over.mono_of_mono_left _
  constructor
  · rintro ⟨z, rfl⟩
    rw [Category.assoc, supportedNativeSubgroupInclusion_comp]
    exact (IdentitySubgroup.Construction.identitySubgroupInclusion_points A F R T t _).mp
      ⟨z, rfl, fun w hw => (cancel_mono (IdentitySubgroup.Construction.identitySubgroupInclusion A F R)).mp hw⟩
  · intro h
    obtain ⟨z, hz, _⟩ := (IdentitySubgroup.Construction.identitySubgroupInclusion_points A F R T t _).mpr h
    refine ⟨z, (cancel_mono (OppositeKernel.Construction.torsionBlockInclusion n p)).mp ?_⟩
    rw [Category.assoc, supportedNativeSubgroupInclusion_comp]
    exact hz

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.SupportedIntrinsicSubgroup.Construction
