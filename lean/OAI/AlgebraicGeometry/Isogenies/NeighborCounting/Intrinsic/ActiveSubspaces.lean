import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.SubspaceCoordinates

/-! # Active Subspaces -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.ActiveSubspaces

/-! Active subspaces in higher native torsion are transported to the
literal source q-block. Its scalar module is constructed from the actual
torsion equation, and the original ambient inclusion is preserved. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ActiveTorsionChoices OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ActiveTypedSubspaces
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.ActiveLevel OAI.AlgebraicGeometry.Isogenies.NeighborCounting.SubspaceCoordinates

theorem nativeBlockPoint_killed {S : Scheme.{0}} {A T : Over S} [GrpObj A] [IsCommMonObj A]
    (n : ℕ) (p : A ⟶ A) [IsMonHom p] (a : Additive (T ⟶ AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock n p)) : n • a = 0 := by
  apply Additive.toMul.injective
  change a.toMul ^ n = 1
  apply (cancel_mono (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion n p)).mp
  rw [MonObj.pow_comp, MonObj.one_comp, ← MonObj.comp_pow,
    AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion_killed, MonObj.comp_one]

instance nativeBlockPointModule {S : Scheme.{0}} {A T : Over S} [GrpObj A] [IsCommMonObj A]
    (n : ℕ) (p : A ⟶ A) [IsMonHom p] : Module (ZMod n) (Additive (T ⟶ AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock n p)) :=
  AddCommGroup.zmodModule (nativeBlockPoint_killed n p)

def nativeBlockPointLevelEquiv {S : Scheme.{0}} {A T : Over S} [GrpObj A] [IsCommMonObj A]
    (n m : ℕ) (p : A ⟶ A) [IsMonHom p] (h : n = m) :
    Additive (T ⟶ AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock n p) ≃+ Additive (T ⟶ AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock m p) := by
  subst m
  exact AddEquiv.refl _

theorem nativeBlockPointLevelEquiv_inclusion {S : Scheme.{0}} {A T : Over S} [GrpObj A] [IsCommMonObj A]
    (n m : ℕ) (p : A ⟶ A) [IsMonHom p] (h : n = m)
    (a : Additive (T ⟶ AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock n p)) :
    (nativeBlockPointLevelEquiv n m p h a).toMul ≫ AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion m p =
      a.toMul ≫ AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion n p := by
  subst m
  rfl

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [Field K] [NumberField K] {κ : K →+* ℂ} {q : ℕ} [Fact q.Prime]
  (j : PELModuli.CMPoints.Arithmetic.QadicChoice K κ q) (iota : E →+* K) (hsplit : j.HasSplitCoordinates iota)
  {S : Scheme.{0}} {g : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S)
  (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A)
  (T : Over S) (m : ℕ) (hm : 1 ≤ m) (τ : Gal(E/ℚ))

def nativeBlockKilledPrimeEquiv :
    ActiveTorsionChoices.killedSubgroup q (Additive (T ⟶ AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock (q ^ m) (ρ.map (j.projector iota hsplit m τ)))) ≃+
      Additive (T ⟶ AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock q (ρ.map (j.projector iota hsplit 1 τ))) :=
  (ActiveLevel.nativeBlockKilledEquiv A T m hm j iota hsplit ρ τ).trans
    (nativeBlockPointLevelEquiv (q ^ 1) q (ρ.map (j.projector iota hsplit 1 τ)) (pow_one q))

theorem nativeBlockKilledPrimeEquiv_inclusion
    (a : ActiveTorsionChoices.killedSubgroup q (Additive (T ⟶ AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock (q ^ m) (ρ.map (j.projector iota hsplit m τ))))) :
    (nativeBlockKilledPrimeEquiv j iota hsplit A ρ T m hm τ a).toMul ≫
      AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion q (ρ.map (j.projector iota hsplit 1 τ)) =
        a.val.toMul ≫ AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion (q ^ m) (ρ.map (j.projector iota hsplit m τ)) :=
  (nativeBlockPointLevelEquiv_inclusion (q ^ 1) q (ρ.map (j.projector iota hsplit 1 τ)) (pow_one q)
    (ActiveLevel.nativeBlockKilledEquiv A T m hm j iota hsplit ρ τ a)).trans
      (ActiveLevel.nativeBlockKilledEquiv_inclusion A T m hm j iota hsplit ρ τ a)

def nativeActiveSubspaceEquiv (r : ℕ) :
    {V : Submodule (ZMod q)
      (ActiveTorsionChoices.killedSubgroup q (Additive (T ⟶ AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock (q ^ m) (ρ.map (j.projector iota hsplit m τ))))) //
      Module.finrank (ZMod q) V = r} ≃
    {V : Submodule (ZMod q) (Additive (T ⟶ AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock q (ρ.map (j.projector iota hsplit 1 τ)))) //
      Module.finrank (ZMod q) V = r} :=
  SubspaceCoordinates.dimensionSubspaceEquiv (ActiveTypedSubspaces.zmodLinearEquiv q (nativeBlockKilledPrimeEquiv j iota hsplit A ρ T m hm τ)) r

end AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.ActiveSubspaces

namespace AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.ActiveSubspaces.IntrinsicBlockLevelGroupIso

/-! Equal torsion levels give the actual native block group isomorphism,
with the original ambient inclusion and point conversion unchanged. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.ActiveSubspaces

variable {S : Scheme} {A T : Over S} [GrpObj A] [IsCommMonObj A]
  (n m : ℕ) (p : A ⟶ A) [IsMonHom p] (h : n = m)

def nativeBlockLevelGroupIso : Grp.mk (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock n p) ≅ Grp.mk (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock m p) := by
  subst m
  exact Iso.refl _

theorem nativeBlockLevelGroupIso_inclusion :
    (nativeBlockLevelGroupIso n m p h).hom.hom.hom ≫ AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion m p =
      AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion n p := by
  subst m
  change (𝟙 (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock n p)) ≫ AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion n p = AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion n p
  exact Category.id_comp _

theorem nativeBlockLevelGroupIso_points (a : Additive (T ⟶ AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock n p)) :
    (nativeBlockPointLevelEquiv n m p h a).toMul =
      a.toMul ≫ (nativeBlockLevelGroupIso n m p h).hom.hom.hom := by
  subst m
  change a.toMul = a.toMul ≫ 𝟙 (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock n p)
  exact (Category.comp_id _).symm

end AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.ActiveSubspaces.IntrinsicBlockLevelGroupIso

end

end OAI
