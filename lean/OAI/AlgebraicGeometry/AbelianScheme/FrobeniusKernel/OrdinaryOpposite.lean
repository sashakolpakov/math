import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.EtaleDual
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.OrdinaryOppositeModels
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.Multiplicative
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PairedKernels

/-! # Ordinary Opposite -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.OrdinaryOpposite.Construction

noncomputable section

/-!
Relative Frobenius vanishes on the actual paired ordinary kernel:
the chosen multiplicative factor and its opposite Cartier annihilator.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u

section Products

variable {S : Scheme.{u}} (p : ℕ) (hp : p.Prime) (hS : (p : Γ(S, ⊤)) = 0)

theorem product_trivialFrobenius (G H : Grp (Over S))
    (hG : Picard.Homomorphisms.Frobenius.Construction.relativeFrobenius p hp hS G.X = 1)
    (hH : Picard.Homomorphisms.Frobenius.Construction.relativeFrobenius p hp hS H.X = 1) :
    Picard.Homomorphisms.Frobenius.Construction.relativeFrobenius p hp hS (G ⊗ H).X = 1 := by
  let F := Over.pullback (Picard.Homomorphisms.Frobenius.Construction.absoluteFrobenius p hp S hS)
  let c := prodComparison F G.X H.X
  have : IsIso c := inferInstanceAs (IsIso (prodComparison F G.X H.X))
  have : IsMonHom (F.map (fst G.X H.X)) :=
    Functor.map.instIsMonHom (F := F) (f := fst G.X H.X) (G.X ⊗ H.X) G.X
  have : IsMonHom (F.map (snd G.X H.X)) :=
    Functor.map.instIsMonHom (F := F) (f := snd G.X H.X) (G.X ⊗ H.X) H.X
  have : IsMonHom c := by
    change IsMonHom (lift (F.map (fst G.X H.X)) (F.map (snd G.X H.X)))
    infer_instance
  apply (cancel_mono c).mp
  erw [MonObj.one_comp]
  apply CartesianMonoidalCategory.hom_ext
  · erw [Category.assoc, prodComparison_fst, MonObj.one_comp]
    exact ((Picard.Homomorphisms.Group.Construction.relativeFrobeniusNat p hp hS).naturality (fst G.X H.X)).symm.trans
      ((congrArg (fun f => fst G.X H.X ≫ f) hG).trans (MonObj.comp_one _))
  · erw [Category.assoc, prodComparison_snd, MonObj.one_comp]
    exact ((Picard.Homomorphisms.Group.Construction.relativeFrobeniusNat p hp hS).naturality (snd G.X H.X)).symm.trans
      ((congrArg (fun f => snd G.X H.X ≫ f) hH).trans (MonObj.comp_one _))

end Products

theorem etaleGroupScheme_power (S : Scheme.{u}) (M : Type u) [Group M]
    (n : ℕ) (hM : ∀ m : M, m ^ n = 1) :
    (𝟙 (EtaleSubgroups.Construction.etaleGroupScheme S M).X) ^ n = 1 := by
  let e := ((EtaleSubgroups.Construction.etaleGroupPointIso S M).app (op (EtaleSubgroups.Construction.etaleGroupScheme S M).X)).groupIsoToMulEquiv
  apply e.injective
  exact (map_pow e _ n).trans ((show e (𝟙 _) ^ n = 1 from by
    apply LocallyConstant.ext
    intro x
    exact hM _).trans e.map_one.symm)

theorem etaleOrdinaryBlock_power (k : Type u) [CommRing k] (p r : ℕ) :
    (𝟙 (OrdinaryBlocks.Construction.etaleOrdinaryBlock k p 1 r).X) ^ p = 1 := by
  apply etaleGroupScheme_power
  intro m
  apply ULift.ext
  apply Multiplicative.toAdd.injective
  change p • m.down.toAdd = 0
  ext j
  change p • m.down.toAdd j = 0
  rw [nsmul_eq_mul]
  have hp : (p : ZMod (p ^ 1)) = 0 :=
    (congrArg (fun n : ℕ => (n : ZMod (p ^ 1))) (pow_one p)).symm.trans (ZMod.natCast_self _)
  rw [hp, zero_mul]

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p] [PerfectRing k p]
variable {B : Grp (Over (Spec (.of k)))} {d r : ℕ}
variable (e : OrdinaryBlocks.Construction.OrdinaryBlockSplitting k B p 1 d r)
variable (P : CartierModel.Construction.CartierCoordinates (.of k) B)
variable (Q : CartierModel.Construction.CartierCoordinates (.of k) (OrdinaryBlocks.Construction.multiplicativeOrdinaryBlock k p 1 d))
variable (V : CartierModel.Construction.CartierCoordinates (.of k) (OrdinaryBlocks.Construction.etaleOrdinaryBlock k p 1 r))

include V in
/-- The opposite annihilator itself has trivial Frobenius. -/
theorem ordinaryOpposite_trivialFrobenius :
    Picard.Homomorphisms.Frobenius.Construction.relativeFrobenius p (Fact.out : p.Prime)
      (Picard.Homomorphisms.Affine.Construction.prime_eq_zero_spec p k (CharP.cast_eq_zero k p))
        (P.annihilatorGroup Q (OrdinaryBlocks.Construction.ordinaryMultiplicativeInclusion k e)).X = 1 := by
  have : Etale (OrdinaryBlocks.Construction.etaleOrdinaryBlock k p 1 r).X.hom := EtaleSubgroups.Construction.etaleGroupScheme_etale _ _
  exact FiniteTorsion.Construction.trivialFrobenius_of_groupIso p (Fact.out : p.Prime)
    (Picard.Homomorphisms.Affine.Construction.prime_eq_zero_spec p k (CharP.cast_eq_zero k p))
    (OrdinaryOppositeModels.Construction.splitOppositeGroupIso e P Q V)
    (V.dual_frobenius_of_etale_torsion p k (etaleOrdinaryBlock_power k p r))

include V in
/-- The assembled chosen/opposite pair, with the actual annihilator
source, is annihilated by relative Frobenius. -/
theorem ordinaryPairedKernel_trivialFrobenius :
    Picard.Homomorphisms.Frobenius.Construction.relativeFrobenius p (Fact.out : p.Prime)
      (Picard.Homomorphisms.Affine.Construction.prime_eq_zero_spec p k (CharP.cast_eq_zero k p))
        (P.pairedKernel Q (OrdinaryBlocks.Construction.ordinaryMultiplicativeInclusion k e)).X = 1 :=
  product_trivialFrobenius p (Fact.out : p.Prime)
    (Picard.Homomorphisms.Affine.Construction.prime_eq_zero_spec p k (CharP.cast_eq_zero k p)) _ _
    (FrobeniusKernel.Multiplicative.Construction.ordinaryMultiplicative_relativeFrobenius p k d)
    (ordinaryOpposite_trivialFrobenius p k e P Q V)

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.OrdinaryOpposite.Construction
