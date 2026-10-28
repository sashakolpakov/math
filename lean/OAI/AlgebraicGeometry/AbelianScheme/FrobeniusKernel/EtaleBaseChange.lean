import OAI.AlgebraicGeometry.Picard.Homomorphisms.Etale
import OAI.AlgebraicGeometry.Picard.Homomorphisms.Group

/-! # Etale Base Change -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.EtaleBaseChange.Construction

noncomputable section

/-! On an etale chosen subgroup, relative Frobenius is invertible.
Its native transport square therefore gives the actual pullback square. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {S : Scheme} (p : ℕ) (hp : p.Prime) (hS : (p : Γ(S, ⊤)) = 0)
variable (H : Over S) [Etale H.hom]

def etaleRelativeFrobeniusIso :
    H ≅ (Over.pullback (Picard.Homomorphisms.Frobenius.Construction.absoluteFrobenius p hp S hS)).obj H := by
  have : IsIso (Picard.Homomorphisms.Frobenius.Construction.relativeFrobenius p hp hS H).left := inferInstance
  have : IsIso ((Over.forget S).map (Picard.Homomorphisms.Frobenius.Construction.relativeFrobenius p hp hS H)) :=
    inferInstanceAs (IsIso (Picard.Homomorphisms.Frobenius.Construction.relativeFrobenius p hp hS H).left)
  have hIso : IsIso (Picard.Homomorphisms.Frobenius.Construction.relativeFrobenius p hp hS H) :=
    isIso_of_reflects_iso (Picard.Homomorphisms.Frobenius.Construction.relativeFrobenius p hp hS H) (Over.forget S)
  exact @asIso (Over S) _ _ _ (Picard.Homomorphisms.Frobenius.Construction.relativeFrobenius p hp hS H) hIso

theorem etaleRelativeFrobeniusIso_hom :
    (etaleRelativeFrobeniusIso p hp hS H).hom = Picard.Homomorphisms.Frobenius.Construction.relativeFrobenius p hp hS H := rfl

variable {H' B B' : Over S} (e : H ≅ H')

def etaleFrobeniusBaseChangeIso :
    (Over.pullback (Picard.Homomorphisms.Frobenius.Construction.absoluteFrobenius p hp S hS)).obj H ≅ H' :=
  (etaleRelativeFrobeniusIso p hp hS H).symm ≪≫ e

theorem etaleFrobeniusBaseChangeIso_inclusion (i : H ⟶ B) (i' : H' ⟶ B')
    (a : (Over.pullback (Picard.Homomorphisms.Frobenius.Construction.absoluteFrobenius p hp S hS)).obj B ⟶ B')
    (he : e.hom ≫ i' = i ≫ Picard.Homomorphisms.Frobenius.Construction.relativeFrobenius p hp hS B ≫ a) :
    (etaleFrobeniusBaseChangeIso p hp hS H e).hom ≫ i' =
      (Over.pullback (Picard.Homomorphisms.Frobenius.Construction.absoluteFrobenius p hp S hS)).map i ≫ a := by
  let F := etaleRelativeFrobeniusIso p hp hS H
  change (F.inv ≫ e.hom) ≫ i' = _
  have hn : i ≫ Picard.Homomorphisms.Frobenius.Construction.relativeFrobenius p hp hS B =
      Picard.Homomorphisms.Frobenius.Construction.relativeFrobenius p hp hS H ≫ (Over.pullback (Picard.Homomorphisms.Frobenius.Construction.absoluteFrobenius p hp S hS)).map i :=
    (Picard.Homomorphisms.Group.Construction.relativeFrobeniusNat p hp hS).naturality i
  have hn' : i ≫ Picard.Homomorphisms.Frobenius.Construction.relativeFrobenius p hp hS B =
      F.hom ≫ (Over.pullback (Picard.Homomorphisms.Frobenius.Construction.absoluteFrobenius p hp S hS)).map i :=
    hn.trans (congrArg (fun z => z ≫ (Over.pullback (Picard.Homomorphisms.Frobenius.Construction.absoluteFrobenius p hp S hS)).map i)
      (etaleRelativeFrobeniusIso_hom p hp hS H).symm)
  exact (Category.assoc F.inv e.hom i').trans
    ((congrArg (fun z => F.inv ≫ z) he).trans
      ((congrArg (fun z => F.inv ≫ z)
        ((Category.assoc i (Picard.Homomorphisms.Frobenius.Construction.relativeFrobenius p hp hS B) a).symm.trans
          (congrArg (fun z => z ≫ a) hn'))).trans
        ((Category.assoc F.inv (F.hom ≫ (Over.pullback (Picard.Homomorphisms.Frobenius.Construction.absoluteFrobenius p hp S hS)).map i) a).symm.trans
          (congrArg (fun z => z ≫ a) (F.inv_hom_id_assoc _)))))

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.EtaleBaseChange.Construction
