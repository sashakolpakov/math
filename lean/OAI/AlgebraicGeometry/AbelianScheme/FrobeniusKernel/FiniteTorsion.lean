import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.HeightOne
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CartierModel

/-! # Finite Torsion -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.FiniteTorsion.Construction

noncomputable section

/-!
Pass the height-one torsion calculation from Hopf coordinates to the
original finite commutative group scheme. Coordinates are extracted from
finite flatness; their compatibility with Frobenius is proved naturally.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open scoped _root_.CategoryTheory.MonObj

universe u

section Transport

variable {S : Scheme.{u}} (p : ℕ) (hp : p.Prime) (hS : (p : Γ(S, ⊤)) = 0)
variable {G H : Grp (Over S)}

theorem trivialFrobenius_of_groupIso (e : G ≅ H)
    (hH : Picard.Homomorphisms.Frobenius.Construction.relativeFrobenius p hp hS H.X = 1) :
    Picard.Homomorphisms.Frobenius.Construction.relativeFrobenius p hp hS G.X = 1 := by
  let F := Over.pullback (Picard.Homomorphisms.Frobenius.Construction.absoluteFrobenius p hp S hS)
  let j : Picard.Homomorphisms.Frobenius.Construction.frobeniusTwist p hp hS G.X ⟶ Picard.Homomorphisms.Frobenius.Construction.frobeniusTwist p hp hS H.X :=
    F.map e.hom.hom.hom
  have : IsIso j := inferInstanceAs (IsIso (F.map e.hom.hom.hom))
  have : IsMonHom j := Functor.map.instIsMonHom (F := F) (f := e.hom.hom.hom) G.X H.X
  apply (cancel_mono j).mp
  have hn := (Picard.Homomorphisms.Group.Construction.relativeFrobeniusNat p hp hS).naturality e.hom.hom.hom
  exact hn.symm.trans
    ((congrArg (fun f => e.hom.hom.hom ≫ f) hH).trans
      ((MonObj.comp_one e.hom.hom.hom).trans (MonObj.one_comp j).symm))

theorem group_power_of_iso (e : G ≅ H) (n : ℕ) (hG : (𝟙 G.X) ^ n = 1) : (𝟙 H.X) ^ n = 1 := by
  let a : H.X ⟶ G.X := e.inv.hom.hom
  let b : G.X ⟶ H.X := e.hom.hom.hom
  have hb : IsMonHom b := inferInstanceAs (IsMonHom e.hom.hom.hom)
  have he : a ≫ b = 𝟙 H.X := congrArg (fun f : H ⟶ H => f.hom.hom) e.inv_hom_id
  have ha : a ^ n = 1 :=
    (congrArg (fun f => f ^ n) (Category.comp_id a)).symm.trans
      ((MonObj.comp_pow (𝟙 G.X) n a).symm.trans
        ((congrArg (fun f => a ≫ f) hG).trans (MonObj.comp_one a)))
  exact (congrArg (fun f => f ^ n) he).symm.trans
    ((MonObj.pow_comp a n b).symm.trans
      ((congrArg (fun f => f ≫ b) ha).trans (MonObj.one_comp b)))

end Transport

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p] [PerfectRing k p]
variable (G : Grp (Over (Spec (.of k)))) [IsCommMonObj G.X]
variable [IsFinite G.X.hom] [Flat G.X.hom] [LocallyOfFinitePresentation G.X.hom]

/-- A native finite commutative group scheme with trivial Frobenius is
killed by p, without selecting or assuming a coordinate presentation. -/
theorem finiteGroup_killed_of_trivial_frobenius
    (hG : Picard.Homomorphisms.Frobenius.Construction.relativeFrobenius p (Fact.out : p.Prime)
      (Picard.Homomorphisms.Affine.Construction.prime_eq_zero_spec p k (CharP.cast_eq_zero k p)) G.X = 1) :
    (𝟙 G.X) ^ p = 1 := by
  let P := CartierModel.Construction.cartierCoordinates (.of k) G
  have : Coalgebra.IsCocomm k P.algebra := P.cocommutative
  have : Module.Finite k P.algebra := P.finite
  have hP := trivialFrobenius_of_groupIso p (Fact.out : p.Prime)
    (Picard.Homomorphisms.Affine.Construction.prime_eq_zero_spec p k (CharP.cast_eq_zero k p)) P.comparison hG
  have hpower := HeightOne.Construction.affineGroup_killed_of_trivial_frobenius p k P.algebra hP
  exact group_power_of_iso P.comparison p hpower

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.FiniteTorsion.Construction
