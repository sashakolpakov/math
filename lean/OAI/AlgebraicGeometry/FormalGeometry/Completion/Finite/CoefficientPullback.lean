import OAI.AlgebraicGeometry.FormalGeometry.Completion.Finite.CoefficientCohomology

/-! # Coefficient Pullback -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.Finite.CoefficientPullback.Construction

noncomputable section

/-!
# Completion: finite reduction commutes with actual cohomology pullback

The finite-coefficient pullback uses the same exact inverse-image functor
as integral cohomology. Reduction commutes with the coefficient comparison,
and hence with pullback in every cohomological degree.
-/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry Abelian

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

variable (ℓ n : ℕ) [Fact ℓ.Prime] {X Y : Scheme.{u}}

/-- Finite coefficient functions restrict along base-change projections. -/
def proEtFiniteCoefficientToPushforward (f : X ⟶ Y) :
    CoefficientSheaf.Construction.finiteEllAdicCoefficient ℓ n Y ⟶
      ((ProetalePullback.Construction.proEtBaseChange f).sheafPushforwardContinuous Ab.{u + 1}
        (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X)).obj
          (CoefficientSheaf.Construction.finiteEllAdicCoefficient ℓ n X) where
  hom := Functor.whiskerRight
    (Functor.whiskerRight (NatTrans.op (ProetalePullback.Construction.proEtBaseChangeProjection f))
      (continuousMapPresheafAb (ZMod (ℓ ^ n)))) AddCommGrpCat.uliftFunctor

/-- The comparison from inverse image to actual finite coefficients. -/
def proEtFiniteCoefficientPullback (f : X ⟶ Y) :
    (ProetalePullback.Construction.proEtSheafPullback f).obj (CoefficientSheaf.Construction.finiteEllAdicCoefficient ℓ n Y) ⟶
      CoefficientSheaf.Construction.finiteEllAdicCoefficient ℓ n X :=
  (((ProetalePullback.Construction.proEtBaseChange f).sheafAdjunctionContinuous Ab.{u + 1}
    (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X)).homEquiv _ _).symm
      (proEtFiniteCoefficientToPushforward ℓ n f)

theorem proEtFiniteCoefficientToPushforward_reduction (f : X ⟶ Y) :
    CoefficientSheaf.Construction.finiteEllAdicReduction ℓ n Y ≫ proEtFiniteCoefficientToPushforward ℓ n f =
      ProetalePullback.Construction.proEtCoefficientToPushforward ℓ f ≫
        ((ProetalePullback.Construction.proEtBaseChange f).sheafPushforwardContinuous Ab.{u + 1}
          (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X)).map
            (CoefficientSheaf.Construction.finiteEllAdicReduction ℓ n X) := by
  ext U s
  rfl

theorem proEtFiniteCoefficientPullback_reduction (f : X ⟶ Y) :
    (ProetalePullback.Construction.proEtSheafPullback f).map (CoefficientSheaf.Construction.finiteEllAdicReduction ℓ n Y) ≫
      proEtFiniteCoefficientPullback ℓ n f =
        ProetalePullback.Construction.proEtCoefficientPullback ℓ f ≫ CoefficientSheaf.Construction.finiteEllAdicReduction ℓ n X := by
  exact ((ProetalePullback.Construction.proEtBaseChange f).sheafAdjunctionContinuous Ab.{u + 1}
    (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X)).homEquiv_naturality_right_square
      (CoefficientSheaf.Construction.finiteEllAdicReduction ℓ n Y) (proEtFiniteCoefficientToPushforward ℓ n f)
      (ProetalePullback.Construction.proEtCoefficientToPushforward ℓ f) (CoefficientSheaf.Construction.finiteEllAdicReduction ℓ n X)
      (proEtFiniteCoefficientToPushforward_reduction ℓ n f)

/-- Pullback on the actual finite-coefficient sheaf cohomology groups. -/
def finiteEllAdicPullback (f : X ⟶ Y) (d : ℕ) :
    (CoefficientSheaf.Construction.finiteEllAdicCoefficient ℓ n Y).H d →+ (CoefficientSheaf.Construction.finiteEllAdicCoefficient ℓ n X).H d :=
  ((Ext.mk₀ (proEtFiniteCoefficientPullback ℓ n f)).postcomp
      (ProetalePullback.Construction.proEtIntegerConstant X) (add_zero d)).comp
    (((Ext.mk₀ ((ProetalePullback.Construction.proEtConstantPullbackIso f).inv.app
        (AddCommGrpCat.of (ULift.{u + 1} ℤ)))).precomp
        ((ProetalePullback.Construction.proEtSheafPullback f).obj (CoefficientSheaf.Construction.finiteEllAdicCoefficient ℓ n Y)) (zero_add d)).comp
      ((ProetalePullback.Construction.proEtSheafPullback f).mapExtAddHom (ProetalePullback.Construction.proEtIntegerConstant Y)
        (CoefficientSheaf.Construction.finiteEllAdicCoefficient ℓ n Y) d))

omit [Fact ℓ.Prime] in
theorem finiteEllAdicPullback_apply (f : X ⟶ Y) (d : ℕ)
    (x : (CoefficientSheaf.Construction.finiteEllAdicCoefficient ℓ n Y).H d) :
    finiteEllAdicPullback ℓ n f d x =
      ((Ext.mk₀ ((ProetalePullback.Construction.proEtConstantPullbackIso f).inv.app
          (AddCommGrpCat.of (ULift.{u + 1} ℤ)))).comp
          (x.mapExactFunctor (ProetalePullback.Construction.proEtSheafPullback f)) (zero_add d)).comp
        (Ext.mk₀ (proEtFiniteCoefficientPullback ℓ n f)) (add_zero d) := rfl

/-- Finite reduction commutes with actual integral cohomology pullback. -/
theorem integralEllAdicFiniteReduction_pullback (f : X ⟶ Y) (d : ℕ)
    (x : Y.EllAdicCohomology ℓ d) :
    finiteEllAdicPullback ℓ n f d (CoefficientCohomology.Construction.integralEllAdicFiniteReduction ℓ n Y d x) =
      CoefficientCohomology.Construction.integralEllAdicFiniteReduction ℓ n X d (ProetalePullback.Construction.integralEllAdicPullback ℓ f d x) := by
  change (ProetalePullback.Construction.liftedEllAdicCoefficient ℓ Y).H d at x
  change finiteEllAdicPullback ℓ n f d
      (x.comp (Ext.mk₀ (CoefficientSheaf.Construction.finiteEllAdicReduction ℓ n Y)) (add_zero d)) =
    (ProetalePullback.Construction.integralEllAdicPullback ℓ f d x).comp
      (Ext.mk₀ (CoefficientSheaf.Construction.finiteEllAdicReduction ℓ n X)) (add_zero d)
  erw [finiteEllAdicPullback_apply, CohomologyPullback.Construction.integralEllAdicPullback_apply]
  simp only [Ext.mapExactFunctor_comp,
    Ext.mapExactFunctor_mk₀, Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀,
    proEtFiniteCoefficientPullback_reduction]

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.Finite.CoefficientPullback.Construction
