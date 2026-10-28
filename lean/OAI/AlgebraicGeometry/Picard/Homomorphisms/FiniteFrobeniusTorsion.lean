import OAI.AlgebraicGeometry.Picard.Homomorphisms.FiniteHopfPresentation
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.HeightOne

/-! # Finite Frobenius Torsion -/

namespace OAI.AlgebraicGeometry.Picard.Homomorphisms.FiniteFrobeniusTorsion

noncomputable section

/-! Trivial Frobenius kills multiplication by p on an actual finite
commutative group scheme over a perfect field. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open scoped _root_.CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency.types false

namespace Construction

universe u

theorem trivialFrobenius_of_groupIso {S : Scheme.{u}}
    (p : ℕ) (hp : p.Prime) (hS : (p : Γ(S, ⊤)) = 0)
    {G H : Grp (Over S)} (e : G ≅ H) (hH : Frobenius.Construction.relativeFrobenius p hp hS H.X = 1) :
    Frobenius.Construction.relativeFrobenius p hp hS G.X = 1 := by
  let F := Over.pullback (Frobenius.Construction.absoluteFrobenius p hp S hS)
  let j : Frobenius.Construction.frobeniusTwist p hp hS G.X ⟶ Frobenius.Construction.frobeniusTwist p hp hS H.X := F.map e.hom.hom.hom
  have : IsIso j := inferInstanceAs (IsIso (F.map e.hom.hom.hom))
  have : IsMonHom j := Functor.map.instIsMonHom (F := F) (f := e.hom.hom.hom) G.X H.X
  apply (cancel_mono j).mp
  have hn := (Group.Construction.relativeFrobeniusNat p hp hS).naturality e.hom.hom.hom
  exact hn.symm.trans
    ((congrArg (fun f => e.hom.hom.hom ≫ f) hH).trans
      ((MonObj.comp_one e.hom.hom.hom).trans (MonObj.one_comp j).symm))

theorem group_power_of_iso {S : Scheme.{u}} {G H : Grp (Over S)}
    (e : G ≅ H) (n : ℕ) (hG : (𝟙 G.X) ^ n = 1) : (𝟙 H.X) ^ n = 1 := by
  let a : H.X ⟶ G.X := e.inv.hom.hom
  let b : G.X ⟶ H.X := e.hom.hom.hom
  have : IsMonHom b := inferInstanceAs (IsMonHom e.hom.hom.hom)
  have he : a ≫ b = 𝟙 H.X := congrArg (fun f : H ⟶ H => f.hom.hom) e.inv_hom_id
  have ha : a ^ n = 1 :=
    (congrArg (fun f => f ^ n) (Category.comp_id a)).symm.trans
      ((MonObj.comp_pow (𝟙 G.X) n a).symm.trans
        ((congrArg (fun f => a ≫ f) hG).trans (MonObj.comp_one a)))
  exact (congrArg (fun f => f ^ n) he).symm.trans
    ((MonObj.pow_comp a n b).symm.trans
      ((congrArg (fun f => f ≫ b) ha).trans (MonObj.one_comp b)))

theorem finiteGroup_killed_of_trivial_frobenius
    (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p] [PerfectRing k p]
    (G : Grp (Over (Spec (.of k)))) [IsCommMonObj G.X] [IsFinite G.X.hom]
    (hG : Frobenius.Construction.relativeFrobenius p Fact.out
      (Affine.Construction.prime_eq_zero_spec p k (CharP.cast_eq_zero k p)) G.X = 1) :
    (𝟙 G.X) ^ p = 1 := by
  obtain ⟨A, hf, hc, ⟨e⟩⟩ := FiniteHopfPresentation.Construction.finite_commutative_hopfPresentation k G
  have : Module.Finite k A := hf
  have : Coalgebra.IsCocomm k A := hc
  have hA := trivialFrobenius_of_groupIso p Fact.out
    (Affine.Construction.prime_eq_zero_spec p k (CharP.cast_eq_zero k p)) e hG
  exact group_power_of_iso e p (AbelianScheme.FrobeniusKernel.HeightOne.Construction.affineGroup_killed_of_trivial_frobenius p k A hA)

end Construction

end

end OAI.AlgebraicGeometry.Picard.Homomorphisms.FiniteFrobeniusTorsion
