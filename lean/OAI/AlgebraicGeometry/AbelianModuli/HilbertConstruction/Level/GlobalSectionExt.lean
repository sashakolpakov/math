import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Level.GlobalSections
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Level.Transport
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ConstantScheme.Iff

/-! # Global Section Ext -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! The actual constant-label sections determine an ordered full level.
The proof uses the open fibers of each locally constant label, so it
applies to arbitrary schemes, including disconnected nonreduced bases. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj
universe u

variable {S : Scheme.{u}} {g N : ℕ} {A B : Abelian.Schemes.AbelianScheme g S}

theorem Abelian.Schemes.AbelianScheme.fullLevelGlobalSection_one (level : A.FullLevel N) :
    A.fullLevelGlobalSection level 1 = (η[A.scheme]).left := by
  have h := congrArg (fun x : A.torsionPoints N (Over.mk (𝟙 S)) => x.val)
    (map_one (level.hom.app (.op (Over.mk (𝟙 S)))).hom)
  exact congrArg Over.Hom.left (h.trans (MonObj.one_eq_one A.scheme).symm)

theorem Abelian.Schemes.AbelianScheme.fullLevelGlobalSection_transport (level : A.FullLevel N)
    (e : A.scheme ≅ B.scheme) [IsMonHom e.hom]
    (c : Multiplicative (Fin (2 * g) → ZMod N)) :
    B.fullLevelGlobalSection (level.transport e) c =
      A.fullLevelGlobalSection level c ≫ e.hom.left :=
  congrArg Over.Hom.left
    (level.transport_basis e (Over.mk (𝟙 S)) (LocallyConstant.const S c))

/-- Values at every constant label determine the full natural level
isomorphism, including its values on all other test schemes. -/
theorem Abelian.Schemes.AbelianScheme.FullLevel.ext_globalSections {level₁ level₂ : A.FullLevel N}
    (h : ∀ c : Multiplicative (Fin (2 * g) → ZMod N),
      A.fullLevelGlobalSection level₁ c = A.fullLevelGlobalSection level₂ c) :
    level₁ = level₂ := by
  apply Abelian.Schemes.AbelianScheme.FullLevel.ext_basis
  intro T c
  let d : LocallyConstant T.left
      (ULift.{u} (Multiplicative (Fin (2 * g) → ZMod N))) :=
    (LocallyConstant.congrRight Equiv.ulift).symm c
  apply Over.OverMorphism.ext
  apply (cancel_epi (ConstantScheme.Iff.locallyConstantFibersIso d).hom).mp
  apply Sigma.hom_ext
  intro i
  rw [ConstantScheme.Iff.locallyConstantFibersIso_ι_hom_assoc, ConstantScheme.Iff.locallyConstantFibersIso_ι_hom_assoc]
  let U : Over S := Over.mk ((ConstantScheme.Iff.locallyConstantFiber d i).ι ≫ T.hom)
  let j : U ⟶ T := Over.homMk (ConstantScheme.Iff.locallyConstantFiber d i).ι rfl
  let b : U ⟶ Over.mk (𝟙 S) := Over.homMk U.hom (Category.comp_id _)
  have hc : c.comap ⟨j.left, j.left.continuous⟩ =
      LocallyConstant.const U.left i.down := by
    apply LocallyConstant.ext
    intro x
    exact congrArg ULift.down x.property
  have hj₁ := congrArg (fun z : A.torsionPoints N U => z.val.left)
    (ConcreteCategory.congr_hom (level₁.hom.naturality j.op) c)
  have hj₂ := congrArg (fun z : A.torsionPoints N U => z.val.left)
    (ConcreteCategory.congr_hom (level₂.hom.naturality j.op) c)
  change (level₁.hom.app (.op U) (c.comap ⟨j.left, j.left.continuous⟩)).val.left =
    j.left ≫ (level₁.hom.app (.op T) c).val.left at hj₁
  change (level₂.hom.app (.op U) (c.comap ⟨j.left, j.left.continuous⟩)).val.left =
    j.left ≫ (level₂.hom.app (.op T) c).val.left at hj₂
  rw [hc] at hj₁ hj₂
  have hb₁ := congrArg (fun z : A.torsionPoints N U => z.val.left)
    (ConcreteCategory.congr_hom (level₁.hom.naturality b.op)
      (LocallyConstant.const S i.down))
  have hb₂ := congrArg (fun z : A.torsionPoints N U => z.val.left)
    (ConcreteCategory.congr_hom (level₂.hom.naturality b.op)
      (LocallyConstant.const S i.down))
  change (level₁.hom.app (.op U) (LocallyConstant.const U.left i.down)).val.left =
    b.left ≫ A.fullLevelGlobalSection level₁ i.down at hb₁
  change (level₂.hom.app (.op U) (LocallyConstant.const U.left i.down)).val.left =
    b.left ≫ A.fullLevelGlobalSection level₂ i.down at hb₂
  exact hj₁.symm.trans (hb₁.trans
    ((congrArg (fun z => b.left ≫ z) (h i.down)).trans (hb₂.symm.trans hj₂)))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
