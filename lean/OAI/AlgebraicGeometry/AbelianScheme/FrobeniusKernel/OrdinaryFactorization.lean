import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.OrdinaryOpposite
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.Ordinary
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.MultiplicativeDual

/-! # Ordinary Factorization -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.OrdinaryFactorization.Construction

noncomputable section

/-!
Every group with trivial Frobenius maps into the prescribed paired
ordinary kernel. The opposite factor is detected by restriction to the
etale Cartier dual of the chosen multiplicative factor.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

variable {S : Scheme.{u}} (p : ℕ) (hp : p.Prime) (hS : (p : Γ(S, ⊤)) = 0)

theorem splitFactor_of_trivialFrobenius
    {B M E T : Grp (Over S)} (e : B ≅ M ⊗ E) [Etale E.X.hom]
    (f : T ⟶ B) (hT : Picard.Homomorphisms.Frobenius.Construction.relativeFrobenius p hp hS T.X = 1) :
    ∃ a : T.X ⟶ M.X, a ≫ (AnnihilatorSheaf.Construction.splitFirstInclusion M E ≫ e.inv).hom.hom = f.hom.hom := by
  let b : T.X ⟶ M.X ⊗ E.X := f.hom.hom ≫ e.hom.hom.hom
  have : IsMonHom (b ≫ snd M.X E.X) := inferInstance
  have hz : b ≫ snd M.X E.X = 1 := Ordinary.Construction.map_to_etale_of_trivial_frobenius p hp hS _ hT
  refine ⟨b ≫ fst M.X E.X, ?_⟩
  have h : (b ≫ fst M.X E.X) ≫ (AnnihilatorSheaf.Construction.splitFirstInclusion M E).hom.hom = b := by
    apply CartesianMonoidalCategory.hom_ext
    · change ((b ≫ fst M.X E.X) ≫ lift (𝟙 M.X) (1 : M.X ⟶ E.X)) ≫ fst M.X E.X = _
      rw [Category.assoc, lift_fst, Category.comp_id]
    · change ((b ≫ fst M.X E.X) ≫ lift (𝟙 M.X) (1 : M.X ⟶ E.X)) ≫ snd M.X E.X = _
      rw [Category.assoc, lift_snd, MonObj.comp_one]
      exact hz.symm
  have he : e.hom.hom.hom ≫ e.inv.hom.hom = 𝟙 B.X :=
    congrArg (fun g : B ⟶ B => g.hom.hom) e.hom_inv_id
  change (b ≫ fst M.X E.X) ≫ (AnnihilatorSheaf.Construction.splitFirstInclusion M E).hom.hom ≫ e.inv.hom.hom = _
  rw [← Category.assoc, h]
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun g => f.hom.hom ≫ g) he).trans (Category.comp_id _))

theorem annihilatorFactor_of_trivialFrobenius
    {R : CommRingCat.{u}} {B M T : Grp (Over (Spec R))}
    (hR : (p : Γ(Spec R, ⊤)) = 0)
    (P : CartierModel.Construction.CartierCoordinates R B) (Q : CartierModel.Construction.CartierCoordinates R M) (i : M ⟶ B)
    [Etale Q.dualGroup.X.hom] (f : T ⟶ P.dualGroup)
    (hT : Picard.Homomorphisms.Frobenius.Construction.relativeFrobenius p hp hR T.X = 1) :
    ∃ a : T.X ⟶ (P.annihilatorGroup Q i).X,
      a ≫ (P.annihilatorInclusion Q i).hom.hom = f.hom.hom := by
  let r := (P.restriction Q i).hom.hom
  have : IsMonHom (f.hom.hom ≫ r) := inferInstance
  have hz : f.hom.hom ≫ r = 1 := Ordinary.Construction.map_to_etale_of_trivial_frobenius p hp hR _ hT
  let a := (Picard.PoincareBundle.Kernel.Scheme.kernelPointsEquiv r T.X).symm ⟨f.hom.hom, hz⟩
  refine ⟨a, ?_⟩
  rw [P.annihilatorInclusion_eq Q i]
  exact congrArg Subtype.val ((Picard.PoincareBundle.Kernel.Scheme.kernelPointsEquiv r T.X).apply_symm_apply _)

theorem pairedFactor_of_trivialFrobenius
    {k : Type u} [Field k] {B M E C T : Grp (Over (Spec (.of k)))}
    (hk : (p : Γ(Spec (.of k), ⊤)) = 0) (e : B ≅ M ⊗ E)
    (P : CartierModel.Construction.CartierCoordinates (.of k) B) (Q : CartierModel.Construction.CartierCoordinates (.of k) M)
    (pairing : C ≅ P.dualGroup) [Etale E.X.hom] [Etale Q.dualGroup.X.hom]
    (f : T ⟶ B ⊗ C) (hT : Picard.Homomorphisms.Frobenius.Construction.relativeFrobenius p hp hk T.X = 1) :
    ∃ a : T.X ⟶ (P.pairedKernel Q (AnnihilatorSheaf.Construction.splitFirstInclusion M E ≫ e.inv)).X,
      a ≫ (P.pairedKernelInclusion Q (AnnihilatorSheaf.Construction.splitFirstInclusion M E ≫ e.inv) pairing).hom.hom =
        f.hom.hom := by
  let i := AnnihilatorSheaf.Construction.splitFirstInclusion M E ≫ e.inv
  let π₁ : B ⊗ C ⟶ B := Grp.homMk (fst B.X C.X)
  let f₁ : T ⟶ B := f ≫ π₁
  let f₂ : T ⟶ P.dualGroup := f ≫ AnnihilatorSheaf.Construction.splitSecondProjection B C ≫ pairing.hom
  obtain ⟨a, ha⟩ := splitFactor_of_trivialFrobenius p hp hk e f₁ hT
  obtain ⟨b, hb⟩ := annihilatorFactor_of_trivialFrobenius p hp hk P Q i f₂ hT
  refine ⟨lift a b, ?_⟩
  apply CartesianMonoidalCategory.hom_ext
  · change (lift a b ≫ (i.hom.hom ⊗ₘ (P.oppositeInclusion Q i pairing).hom.hom)) ≫ fst B.X C.X = _
    rw [Category.assoc, tensorHom_fst, ← Category.assoc, lift_fst]
    exact ha
  · change (lift a b ≫ (i.hom.hom ⊗ₘ (P.oppositeInclusion Q i pairing).hom.hom)) ≫ snd B.X C.X = _
    rw [Category.assoc, tensorHom_snd, ← Category.assoc, lift_snd]
    change b ≫ (P.annihilatorInclusion Q i).hom.hom ≫ pairing.inv.hom.hom = _
    rw [← Category.assoc, hb]
    have he : pairing.hom.hom.hom ≫ pairing.inv.hom.hom = 𝟙 C.X :=
      congrArg (fun g : C ⟶ C => g.hom.hom) pairing.hom_inv_id
    change (f.hom.hom ≫ snd B.X C.X ≫ pairing.hom.hom.hom) ≫ pairing.inv.hom.hom = _
    rw [Category.assoc, Category.assoc, he, Category.comp_id]

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.OrdinaryFactorization.Construction
