import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.GroupHomExt
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.MultiplicativeGeometricTorsion

/-! # Neutral Characters -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.NeutralCharacters.CM

noncomputable section

/-! Characters of a finite q-primary group scheme in characteristic q
remain distinct when restricted to its constructed connected factor. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj
open OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme

open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.GroupRetraction.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.GroupDecomposition.CM

universe u
variable {k : Type u} [Field k] [IsAlgClosed k]
  (A : Grp (Over (Spec (.of k)))) [IsFinite A.X.hom]

attribute [local instance] Picard.PoincareBundle.Kernel.Scheme.kernelGroup

def inclusion : Finite.GroupDecomposition.CM.neutralPart A ⟶ A :=
  Grp.ofHom (A := Picard.PoincareBundle.Kernel.Scheme.kernelObject (Finite.GroupRetraction.CM.componentMap A)) (B := A.X)
    (Picard.PoincareBundle.Kernel.Scheme.kernelInclusion (Finite.GroupRetraction.CM.componentMap A))

def restrict (f : A ⟶ AbelianScheme.CartierDuality.CharacterSheaf.Construction.Schemes.multiplicativeGroupOver (Spec (.of k))) :
    Finite.GroupDecomposition.CM.neutralPart A ⟶ AbelianScheme.CartierDuality.CharacterSheaf.Construction.Schemes.multiplicativeGroupOver (Spec (.of k)) := inclusion A ≫ f

def restrictionHom : (A ⟶ AbelianScheme.CartierDuality.CharacterSheaf.Construction.Schemes.multiplicativeGroupOver (Spec (.of k))) →*
    (Finite.GroupDecomposition.CM.neutralPart A ⟶ AbelianScheme.CartierDuality.CharacterSheaf.Construction.Schemes.multiplicativeGroupOver (Spec (.of k))) where
  toFun := restrict A
  map_one' := MonObj.comp_one (inclusion A)
  map_mul' f g := MonObj.comp_mul (inclusion A) f g

theorem restrict_injective [IsCommMonObj A.X]
    (q : ℕ) [Fact q.Prime] [CharP k q] (n : ℕ)
    (hkill : ∀ p : Over.mk (𝟙 (Spec (.of k))) ⟶ A.X, p ^ (q ^ n) = 1) :
    Function.Injective (restrict A) := by
  intro f g h
  apply Finite.GroupHomExt.CM.hom_ext A (AbelianScheme.CartierDuality.CharacterSheaf.Construction.Schemes.multiplicativeGroupOver (Spec (.of k))) f g
  · exact congrArg (fun a : Finite.GroupDecomposition.CM.neutralPart A ⟶ AbelianScheme.CartierDuality.CharacterSheaf.Construction.Schemes.multiplicativeGroupOver (Spec (.of k)) =>
      a.hom.hom) h
  · intro p
    have hf : (p ≫ f.hom.hom) ^ (q ^ n) = 1 := by
      rw [← MonObj.pow_comp, hkill p, MonObj.one_comp]
    have hg : (p ≫ g.hom.hom) ^ (q ^ n) = 1 := by
      rw [← MonObj.pow_comp, hkill p, MonObj.one_comp]
    exact (MultiplicativeGeometricTorsion.CM.point_eq_one q n _ hf).trans
      (MultiplicativeGeometricTorsion.CM.point_eq_one q n _ hg).symm

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.NeutralCharacters.CM
