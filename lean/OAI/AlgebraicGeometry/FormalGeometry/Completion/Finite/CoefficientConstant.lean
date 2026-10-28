import OAI.AlgebraicGeometry.FormalGeometry.Completion.ProEtale.OpenCover
import OAI.AlgebraicGeometry.FormalGeometry.Completion.Finite.CoefficientSheaf
import Mathlib.CategoryTheory.Sites.LocallyBijective

/-! # Coefficient Constant -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.Finite.CoefficientConstant.Construction

noncomputable section

/-!
# Completion: actual finite coefficients are the constant abelian sheaf

The map sending an element to its constant function is locally bijective:
evaluation proves local injectivity, and the open level sets of a continuous
finite-coefficient function give local lifts. Sheafification therefore gives
the actual constant-coefficient comparison, without assuming it.
-/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry Opposite

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

variable (ℓ n : ℕ) (X : Scheme.{u})

/-- The constant presheaf of finite coefficients, in the cohomology universe. -/
abbrev finiteCoefficientConstantPresheaf : X.ProEtᵒᵖ ⥤ Ab.{u + 1} :=
  (Functor.const X.ProEtᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} (ZMod (ℓ ^ n))))

/-- Constants define actual continuous coefficient functions. -/
def finiteCoefficientConstantMap :
    finiteCoefficientConstantPresheaf ℓ n X ⟶ (CoefficientSheaf.Construction.finiteEllAdicCoefficient ℓ n X).obj where
  app U := AddCommGrpCat.ofHom {
    toFun a := ⟨ContinuousMap.const U.unop.left a.down⟩
    map_zero' := rfl
    map_add' _ _ := rfl }
  naturality _ _ _ := rfl

instance finiteCoefficientConstantMap_locallyInjective :
    Presheaf.IsLocallyInjective (Scheme.ProEt.topology X) (finiteCoefficientConstantMap ℓ n X) where
  equalizerSieve_mem {U} a b h := by
    by_cases hn : Nonempty U.unop.left
    · have hab : a = b := by
        apply ULift.ext
        exact congrArg (fun s : ULift.{u + 1} C(U.unop.left, ZMod (ℓ ^ n)) => s.down hn.some) h
      subst b
      rw [Presheaf.equalizerSieve_self_eq_top]
      exact (Scheme.ProEt.topology X).top_mem _
    · have : IsEmpty U.unop.left := not_nonempty_iff.mp hn
      exact (Scheme.ProEt.topology X).superset_covering bot_le (Scheme.ProEt.bot_mem_topology U.unop)

instance finiteCoefficientConstantMap_locallySurjective :
    Presheaf.IsLocallySurjective (Scheme.ProEt.topology X) (finiteCoefficientConstantMap ℓ n X) where
  imageSieve_mem {U} f := by
    change ULift.{u + 1} C(U.left, ZMod (ℓ ^ n)) at f
    let O : ZMod (ℓ ^ n) → U.left.Opens := fun a =>
      ⟨f.down ⁻¹' {a}, (isOpen_discrete _).preimage f.down.continuous⟩
    let V := U.left.openCoverOfIsOpenCover O (by ext x; simp [O])
    apply (Scheme.ProEt.topology X).superset_covering _ (ProEtale.OpenCover.Construction.proEtaleOpenCover_cover U V)
    apply (Sieve.generate_le_iff _ _).mpr
    rintro W g ⟨a⟩
    refine ⟨⟨a⟩, ?_⟩
    apply ULift.ext
    apply ContinuousMap.ext
    intro x
    exact x.property.symm

/-- The isomorphism from the ordinary constant abelian sheaf to the actual finite coefficient sheaf. -/
def finiteCoefficientConstantIso :
    (constantSheaf (Scheme.ProEt.topology X) Ab.{u + 1}).obj
      (AddCommGrpCat.of (ULift.{u + 1} (ZMod (ℓ ^ n)))) ≅ CoefficientSheaf.Construction.finiteEllAdicCoefficient ℓ n X := by
  have : IsIso ((presheafToSheaf (Scheme.ProEt.topology X) Ab.{u + 1}).map
      (finiteCoefficientConstantMap ℓ n X)) :=
    ((Scheme.ProEt.topology X).W_iff _).mp
      ((Scheme.ProEt.topology X).W_of_isLocallyBijective (finiteCoefficientConstantMap ℓ n X))
  exact asIso ((presheafToSheaf (Scheme.ProEt.topology X) Ab.{u + 1}).map
      (finiteCoefficientConstantMap ℓ n X)) ≪≫
    asIso ((sheafificationAdjunction (Scheme.ProEt.topology X) Ab.{u + 1}).counit.app
      (CoefficientSheaf.Construction.finiteEllAdicCoefficient ℓ n X))

/-- The constructed comparison sends each constant generator to its actual constant function. -/
theorem finiteCoefficientConstantIso_unit :
    toSheafify (Scheme.ProEt.topology X) (finiteCoefficientConstantPresheaf ℓ n X) ≫
      (finiteCoefficientConstantIso ℓ n X).hom.hom = finiteCoefficientConstantMap ℓ n X := by
  change toSheafify (Scheme.ProEt.topology X) (finiteCoefficientConstantPresheaf ℓ n X) ≫
    sheafifyMap (Scheme.ProEt.topology X) (finiteCoefficientConstantMap ℓ n X) ≫
      ((sheafificationAdjunction (Scheme.ProEt.topology X) Ab.{u + 1}).counit.app
        (CoefficientSheaf.Construction.finiteEllAdicCoefficient ℓ n X)).hom = _
  rw [← Category.assoc, ← toSheafify_naturality, Category.assoc,
    sheafificationAdjunction_counit_app_val, toSheafify_sheafifyLift, Category.comp_id]

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.Finite.CoefficientConstant.Construction
