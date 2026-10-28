import OAI.AlgebraicGeometry.FormalGeometry.Completion.Finite.CoefficientPullback
import OAI.AlgebraicGeometry.FormalGeometry.Completion.CohomologyFunctoriality

/-! # Functoriality -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.FiniteCoefficient.Functoriality

noncomputable section

/-! Functoriality of pullback on the actual finite-coefficient pro-étale
cohomology. The coefficient comparison is induced by base-change
projections and retains the existing sheaf and Ext definitions. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.Abelian _root_.AlgebraicGeometry

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

variable {X Y Z : Scheme.{u}}

/-- The coefficient maps respect composition of scheme morphisms. -/
theorem proEtFiniteCoefficientToPushforward_comp (ℓ n : ℕ)
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    AlgebraicGeometry.FormalGeometry.Completion.Finite.CoefficientPullback.Construction.proEtFiniteCoefficientToPushforward ℓ n (f ≫ g) =
      AlgebraicGeometry.FormalGeometry.Completion.Finite.CoefficientPullback.Construction.proEtFiniteCoefficientToPushforward ℓ n g ≫
        ((AlgebraicGeometry.FormalGeometry.Completion.ProetalePullback.Construction.proEtBaseChange g).sheafPushforwardContinuous Ab.{u + 1}
          (Scheme.ProEt.topology Z) (Scheme.ProEt.topology Y)).map
            (AlgebraicGeometry.FormalGeometry.Completion.Finite.CoefficientPullback.Construction.proEtFiniteCoefficientToPushforward ℓ n f) ≫
        (AlgebraicGeometry.FormalGeometry.Completion.PullbackCoherence.Construction.proEtSheafPushforwardCompIso f g).hom.app (AlgebraicGeometry.FormalGeometry.Completion.Finite.CoefficientSheaf.Construction.finiteEllAdicCoefficient ℓ n X) := by
  ext U s
  change ULift.{u + 1} (ContinuousMap U.unop.left (ZMod (ℓ ^ n))) at s
  apply ULift.ext
  apply ContinuousMap.ext
  intro x
  change s.down ((pullback.fst U.unop.hom (f ≫ g)) x) =
    s.down ((pullback.fst U.unop.hom g)
      ((pullback.fst (pullback.snd U.unop.hom g) f)
        (((AlgebraicGeometry.FormalGeometry.Completion.PullbackCoherence.Construction.proEtBaseChangeCompIso f g).hom.app U.unop).left x)))
  exact congrArg (fun h : pullback U.unop.hom (f ≫ g) ⟶ U.unop.left => s.down (h x))
    (MorphismProperty.Over.pullbackComp_left_fst_fst f g U.unop).symm

/-- The coefficient map for the identity agrees with the canonical comparison. -/
theorem proEtFiniteCoefficientToPushforward_id (ℓ n : ℕ) (X : Scheme.{u}) :
    AlgebraicGeometry.FormalGeometry.Completion.Finite.CoefficientPullback.Construction.proEtFiniteCoefficientToPushforward ℓ n (𝟙 X) ≫
      (AlgebraicGeometry.FormalGeometry.Completion.PullbackCoherence.Construction.proEtSheafPushforwardIdIso X).hom.app (AlgebraicGeometry.FormalGeometry.Completion.Finite.CoefficientSheaf.Construction.finiteEllAdicCoefficient ℓ n X) = 𝟙 _ := by
  ext U s
  change ULift.{u + 1} (ContinuousMap U.unop.left (ZMod (ℓ ^ n))) at s
  apply ULift.ext
  apply ContinuousMap.ext
  intro x
  change s.down ((pullback.fst U.unop.hom (𝟙 X))
    (((AlgebraicGeometry.FormalGeometry.Completion.PullbackCoherence.Construction.proEtBaseChangeIdIso X).inv.app U.unop).left x)) = s.down x
  have h : ((AlgebraicGeometry.FormalGeometry.Completion.PullbackCoherence.Construction.proEtBaseChangeIdIso X).inv.app U.unop).left ≫
      pullback.fst U.unop.hom (𝟙 X) = 𝟙 U.unop.left := by
    exact congrArg (fun f => f.left) ((AlgebraicGeometry.FormalGeometry.Completion.PullbackCoherence.Construction.proEtBaseChangeIdIso X).inv_hom_id_app U.unop)
  exact congrArg (fun f : U.unop.left ⟶ U.unop.left => s.down (f x)) h

/-- Composition of the adjoint coefficient maps, with the necessary comparison. -/
theorem proEtFiniteCoefficientPullback_comp (ℓ n : ℕ)
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    (AlgebraicGeometry.FormalGeometry.Completion.PullbackCoherence.Construction.proEtSheafPullbackCompIso f g).hom.app (AlgebraicGeometry.FormalGeometry.Completion.Finite.CoefficientSheaf.Construction.finiteEllAdicCoefficient ℓ n Z) ≫
      AlgebraicGeometry.FormalGeometry.Completion.Finite.CoefficientPullback.Construction.proEtFiniteCoefficientPullback ℓ n (f ≫ g) =
        (AlgebraicGeometry.FormalGeometry.Completion.ProetalePullback.Construction.proEtSheafPullback f).map (AlgebraicGeometry.FormalGeometry.Completion.Finite.CoefficientPullback.Construction.proEtFiniteCoefficientPullback ℓ n g) ≫
          AlgebraicGeometry.FormalGeometry.Completion.Finite.CoefficientPullback.Construction.proEtFiniteCoefficientPullback ℓ n f := by
  unfold AlgebraicGeometry.FormalGeometry.Completion.Finite.CoefficientPullback.Construction.proEtFiniteCoefficientPullback
  rw [proEtFiniteCoefficientToPushforward_comp]
  exact AlgebraicGeometry.FormalGeometry.Completion.AdjunctionCoherence.Construction.adjunction_comp_adjoint
    ((AlgebraicGeometry.FormalGeometry.Completion.ProetalePullback.Construction.proEtBaseChange g).sheafAdjunctionContinuous Ab.{u + 1} _ _)
    ((AlgebraicGeometry.FormalGeometry.Completion.ProetalePullback.Construction.proEtBaseChange f).sheafAdjunctionContinuous Ab.{u + 1} _ _)
    ((AlgebraicGeometry.FormalGeometry.Completion.ProetalePullback.Construction.proEtBaseChange (f ≫ g)).sheafAdjunctionContinuous Ab.{u + 1} _ _)
    (AlgebraicGeometry.FormalGeometry.Completion.PullbackCoherence.Construction.proEtSheafPushforwardCompIso f g)
    (AlgebraicGeometry.FormalGeometry.Completion.Finite.CoefficientPullback.Construction.proEtFiniteCoefficientToPushforward ℓ n g) (AlgebraicGeometry.FormalGeometry.Completion.Finite.CoefficientPullback.Construction.proEtFiniteCoefficientToPushforward ℓ n f)

/-- The adjoint coefficient map for the identity is the identity comparison. -/
theorem proEtFiniteCoefficientPullback_id (ℓ n : ℕ) (X : Scheme.{u}) :
    AlgebraicGeometry.FormalGeometry.Completion.Finite.CoefficientPullback.Construction.proEtFiniteCoefficientPullback ℓ n (𝟙 X) =
      (AlgebraicGeometry.FormalGeometry.Completion.PullbackCoherence.Construction.proEtSheafPullbackIdIso X).hom.app (AlgebraicGeometry.FormalGeometry.Completion.Finite.CoefficientSheaf.Construction.finiteEllAdicCoefficient ℓ n X) := by
  have h : AlgebraicGeometry.FormalGeometry.Completion.Finite.CoefficientPullback.Construction.proEtFiniteCoefficientToPushforward ℓ n (𝟙 X) =
      (AlgebraicGeometry.FormalGeometry.Completion.PullbackCoherence.Construction.proEtSheafPushforwardIdIso X).inv.app (AlgebraicGeometry.FormalGeometry.Completion.Finite.CoefficientSheaf.Construction.finiteEllAdicCoefficient ℓ n X) := by
    rw [← cancel_mono ((AlgebraicGeometry.FormalGeometry.Completion.PullbackCoherence.Construction.proEtSheafPushforwardIdIso X).hom.app
      (AlgebraicGeometry.FormalGeometry.Completion.Finite.CoefficientSheaf.Construction.finiteEllAdicCoefficient ℓ n X)), proEtFiniteCoefficientToPushforward_id,
      Iso.inv_hom_id_app]
    rfl
  unfold AlgebraicGeometry.FormalGeometry.Completion.Finite.CoefficientPullback.Construction.proEtFiniteCoefficientPullback
  rw [h]
  exact AlgebraicGeometry.FormalGeometry.Completion.AdjunctionCoherence.Construction.adjunction_id_adjoint
    ((AlgebraicGeometry.FormalGeometry.Completion.ProetalePullback.Construction.proEtBaseChange (𝟙 X)).sheafAdjunctionContinuous Ab.{u + 1} _ _)
    (AlgebraicGeometry.FormalGeometry.Completion.PullbackCoherence.Construction.proEtSheafPushforwardIdIso X) (AlgebraicGeometry.FormalGeometry.Completion.Finite.CoefficientSheaf.Construction.finiteEllAdicCoefficient ℓ n X)

variable (ℓ n : ℕ) [Fact ℓ.Prime]

omit [Fact (Nat.Prime ℓ)] in
theorem finiteEllAdicPullback_comp (f : X ⟶ Y) (g : Y ⟶ Z) (d : ℕ)
    (x : (AlgebraicGeometry.FormalGeometry.Completion.Finite.CoefficientSheaf.Construction.finiteEllAdicCoefficient ℓ n Z).H d) :
    AlgebraicGeometry.FormalGeometry.Completion.Finite.CoefficientPullback.Construction.finiteEllAdicPullback ℓ n f d (AlgebraicGeometry.FormalGeometry.Completion.Finite.CoefficientPullback.Construction.finiteEllAdicPullback ℓ n g d x) =
      AlgebraicGeometry.FormalGeometry.Completion.Finite.CoefficientPullback.Construction.finiteEllAdicPullback ℓ n (f ≫ g) d x := by
  have h := AlgebraicGeometry.FormalGeometry.Completion.ExtFunctoriality.Construction.ext_transport_comp (AlgebraicGeometry.FormalGeometry.Completion.ProetalePullback.Construction.proEtSheafPullback g) (AlgebraicGeometry.FormalGeometry.Completion.ProetalePullback.Construction.proEtSheafPullback f)
    (AlgebraicGeometry.FormalGeometry.Completion.PullbackCoherence.Construction.proEtSheafPullbackCompIso f g)
    ((AlgebraicGeometry.FormalGeometry.Completion.ProetalePullback.Construction.proEtConstantPullbackIso g).inv.app (AddCommGrpCat.of (ULift.{u + 1} ℤ)))
    (AlgebraicGeometry.FormalGeometry.Completion.Finite.CoefficientPullback.Construction.proEtFiniteCoefficientPullback ℓ n g)
    ((AlgebraicGeometry.FormalGeometry.Completion.ProetalePullback.Construction.proEtConstantPullbackIso f).inv.app (AddCommGrpCat.of (ULift.{u + 1} ℤ)))
    (AlgebraicGeometry.FormalGeometry.Completion.Finite.CoefficientPullback.Construction.proEtFiniteCoefficientPullback ℓ n f)
    ((AlgebraicGeometry.FormalGeometry.Completion.ProetalePullback.Construction.proEtConstantPullbackIso (f ≫ g)).inv.app (AddCommGrpCat.of (ULift.{u + 1} ℤ)))
    (AlgebraicGeometry.FormalGeometry.Completion.Finite.CoefficientPullback.Construction.proEtFiniteCoefficientPullback ℓ n (f ≫ g))
    (AlgebraicGeometry.FormalGeometry.Completion.ConstantCoherence.Construction.proEtConstantPullbackIso_inv_comp f g (AddCommGrpCat.of (ULift.{u + 1} ℤ)))
    (proEtFiniteCoefficientPullback_comp ℓ n f g).symm x
  simp only [AlgebraicGeometry.FormalGeometry.Completion.Finite.CoefficientPullback.Construction.finiteEllAdicPullback_apply]
  exact h

omit [Fact (Nat.Prime ℓ)] in
theorem finiteEllAdicPullback_id (X : Scheme.{u}) (d : ℕ)
    (x : (AlgebraicGeometry.FormalGeometry.Completion.Finite.CoefficientSheaf.Construction.finiteEllAdicCoefficient ℓ n X).H d) :
    AlgebraicGeometry.FormalGeometry.Completion.Finite.CoefficientPullback.Construction.finiteEllAdicPullback ℓ n (𝟙 X) d x = x := by
  have hc : (AlgebraicGeometry.FormalGeometry.Completion.ProetalePullback.Construction.proEtConstantPullbackIso (𝟙 X)).app (AddCommGrpCat.of (ULift.{u + 1} ℤ)) =
      (AlgebraicGeometry.FormalGeometry.Completion.PullbackCoherence.Construction.proEtSheafPullbackIdIso X).app (AlgebraicGeometry.FormalGeometry.Completion.ProetalePullback.Construction.proEtIntegerConstant X) :=
    Iso.ext (AlgebraicGeometry.FormalGeometry.Completion.ConstantCoherence.Construction.proEtConstantPullbackIso_id X (AddCommGrpCat.of (ULift.{u + 1} ℤ)))
  have hi := congrArg Iso.inv hc
  change (AlgebraicGeometry.FormalGeometry.Completion.ProetalePullback.Construction.proEtConstantPullbackIso (𝟙 X)).inv.app (AddCommGrpCat.of (ULift.{u + 1} ℤ)) =
    (AlgebraicGeometry.FormalGeometry.Completion.PullbackCoherence.Construction.proEtSheafPullbackIdIso X).inv.app (AlgebraicGeometry.FormalGeometry.Completion.ProetalePullback.Construction.proEtIntegerConstant X) at hi
  erw [AlgebraicGeometry.FormalGeometry.Completion.Finite.CoefficientPullback.Construction.finiteEllAdicPullback_apply, hi, proEtFiniteCoefficientPullback_id,
    AlgebraicGeometry.FormalGeometry.Completion.ExtFunctoriality.Construction.ext_mapExactFunctor_iso (AlgebraicGeometry.FormalGeometry.Completion.ProetalePullback.Construction.proEtSheafPullback (𝟙 X)) (AlgebraicGeometry.FormalGeometry.Completion.PullbackCoherence.Construction.proEtSheafPullbackIdIso X),
    AlgebraicGeometry.FormalGeometry.Completion.ExtFunctoriality.Construction.ext_mapExactFunctor_id]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.FiniteCoefficient.Functoriality
