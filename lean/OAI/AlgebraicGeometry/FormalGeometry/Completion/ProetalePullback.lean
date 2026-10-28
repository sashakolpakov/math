import Mathlib.AlgebraicGeometry.Sites.ElladicCohomology
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.CategoryTheory.MorphismProperty.OverAdjunction
import Mathlib.CategoryTheory.Sites.Pullback
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map

/-! # Proetale Pullback -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.ProetalePullback.Construction

noncomputable section

/-!
# Completion: pullback on the actual pro-étale sites

Base change along a scheme morphism is continuous and preserves finite
limits. These facts are needed to construct pullback on cohomology.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

variable {X Y : Scheme.{u}}

local instance weaklyEtale_composition :
    MorphismProperty.IsStableUnderComposition (@WeaklyEtale.{u}) :=
  (inferInstance : MorphismProperty.IsMultiplicative (@WeaklyEtale.{u})).toIsStableUnderComposition

local instance weaklyEtale_hasPullbacksAlong (f : X ⟶ Y) :
    MorphismProperty.HasPullbacksAlong (@WeaklyEtale.{u}) f where
  hasPullback _ _ := inferInstance

local instance weaklyEtale_baseChangeAlong (f : X ⟶ Y) :
    MorphismProperty.IsStableUnderBaseChangeAlong (@WeaklyEtale.{u}) f where
  of_isPullback := MorphismProperty.IsStableUnderBaseChange.of_isPullback

/-- Base change on the small pro-étale site. -/
noncomputable def proEtBaseChange (f : X ⟶ Y) : Y.ProEt ⥤ X.ProEt :=
  MorphismProperty.Over.pullback @WeaklyEtale.{u} ⊤ f

instance proEtBaseChange_preservesFiniteLimits (f : X ⟶ Y) :
    PreservesFiniteLimits (proEtBaseChange f) := by
  have : PreservesFiniteLimits (proEtBaseChange f ⋙ Scheme.ProEt.forget X) := by
    change PreservesFiniteLimits (Scheme.ProEt.forget Y ⋙ Over.pullback f)
    infer_instance
  exact preservesFiniteLimits_of_reflects_of_preserves
    (proEtBaseChange f) (Scheme.ProEt.forget X)

instance proEtBaseChange_flat (f : X ⟶ Y) : RepresentablyFlat (proEtBaseChange f) :=
  flat_of_preservesFiniteLimits _

instance proEtForget_cocontinuous (X : Scheme.{u}) :
    (Scheme.ProEt.forget X).IsCocontinuous
      (Scheme.ProEt.topology X) (Scheme.proetaleTopology.over X) := by
  have htop : Scheme.ProEt.topology X =
      (Scheme.ProEt.forget X).restrictedTopology (Scheme.proetaleTopology.over X) :=
    MorphismProperty.toGrothendieck_comap_forget_eq_restrictedTopology
      (P := @WeaklyEtale.{u}) (S := X)
      Scheme.proetalePrecoverage Scheme.proetalePrecoverage_le_precoverage_weaklyEtale
  rw [htop]
  infer_instance

instance proEtBaseChange_continuous (f : X ⟶ Y) :
    (proEtBaseChange f).IsContinuous (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X) := by
  rw [Functor.isContinuous_iff_coverPreserving]
  apply CoverPreserving.of_comp_of_isCocontinuous
    (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X)
    (L := Scheme.proetaleTopology.over X) (Scheme.ProEt.forget X)
  have : (proEtBaseChange f ⋙ Scheme.ProEt.forget X).IsContinuous
      (Scheme.ProEt.topology Y) (Scheme.proetaleTopology.over X) := by
    change (Scheme.ProEt.forget Y ⋙ Over.pullback f).IsContinuous
      (Scheme.ProEt.topology Y) (Scheme.proetaleTopology.over X)
    exact Functor.isContinuous_comp _ _ _ (Scheme.proetaleTopology.over Y) _
  exact CoverPreserving.of_isContinuous _ _ _

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Pointwise left Kan extension, without requiring object and morphism
universes to coincide. This is the universe-general form of mathlib's
`Functor.lanEvaluationIsoColim`, used for the small pro-étale site. -/
noncomputable def largeLanEvaluationIsoColim
    {C : Type*} [Category* C] {D : Type*} [Category* D]
    (E : Type*) [Category* E] (F : C ⥤ D) (U : D)
    [∀ U : D, HasColimitsOfShape (CostructuredArrow F U) E] :
    F.lan ⋙ (evaluation D E).obj U ≅
      (Functor.whiskeringLeft _ _ E).obj (CostructuredArrow.proj F U) ⋙ colim :=
  NatIso.ofComponents (fun G =>
    IsColimit.coconePointUniqueUpToIso
      (Functor.isPointwiseLeftKanExtensionLeftKanExtensionUnit F G U)
      (colimit.isColimit _)) (fun {G₁ G₂} φ => by
    apply (Functor.isPointwiseLeftKanExtensionLeftKanExtensionUnit F G₁ U).hom_ext
    intro T
    have h₁ := fun (G : C ⥤ E) => IsColimit.comp_coconePointUniqueUpToIso_hom
      (Functor.isPointwiseLeftKanExtensionLeftKanExtensionUnit F G U)
      (colimit.isColimit _) T
    have h₂ := congr_app (F.lanUnit.naturality φ) T.left
    dsimp at h₁ h₂ ⊢
    simp only [Category.assoc] at h₁ ⊢
    simp only [Functor.lan, Functor.lanUnit] at h₂ ⊢
    rw [reassoc_of% h₁, NatTrans.naturality_assoc, ← reassoc_of% h₂, h₁,
      ι_colimMap, Functor.whiskerLeft_app]
    rfl)

noncomputable instance proEtPresheafPullback_preservesFiniteLimits (f : X ⟶ Y) :
    PreservesFiniteLimits ((proEtBaseChange f).op.lan :
      (Y.ProEtᵒᵖ ⥤ Ab.{u + 1}) ⥤ (X.ProEtᵒᵖ ⥤ Ab.{u + 1})) := by
  apply preservesFiniteLimits_of_preservesFiniteLimitsOfSize.{u + 1}
  intro J _ _
  apply preservesLimitsOfShape_of_evaluation
    ((proEtBaseChange f).op.lan :
      (Y.ProEtᵒᵖ ⥤ Ab.{u + 1}) ⥤ (X.ProEtᵒᵖ ⥤ Ab.{u + 1})) J
  intro U
  have : IsFiltered (CostructuredArrow (proEtBaseChange f).op U) :=
    IsFiltered.of_equivalence (structuredArrowOpEquivalence (proEtBaseChange f) U.unop)
  have : AB5OfSize.{u, u + 1} Ab.{u + 1} :=
    AB5OfSize_of_univLE.{u, u + 1, u + 1, u + 1} Ab.{u + 1}
  exact preservesLimitsOfShape_of_natIso
    (largeLanEvaluationIsoColim Ab.{u + 1} (proEtBaseChange f).op U).symm

/-- Inverse image of abelian sheaves on the pro-étale sites. -/
noncomputable def proEtSheafPullback (f : X ⟶ Y) :
    Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1} ⥤
      Sheaf (Scheme.ProEt.topology X) Ab.{u + 1} :=
  (proEtBaseChange f).sheafPullback Ab.{u + 1}
    (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X)

instance proEtSheafPullback_leftAdjoint (f : X ⟶ Y) :
    (proEtSheafPullback f).IsLeftAdjoint :=
  ((proEtBaseChange f).sheafAdjunctionContinuous Ab.{u + 1}
    (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X)).isLeftAdjoint

instance proEtSheafPullback_preservesFiniteLimits (f : X ⟶ Y) :
    PreservesFiniteLimits (proEtSheafPullback f) := by
  unfold proEtSheafPullback
  apply Functor.sheafPullbackConstruction.preservesFiniteLimits

instance proEtSheafPullback_preservesFiniteColimits (f : X ⟶ Y) :
    PreservesFiniteColimits (proEtSheafPullback f) := inferInstance

instance proEtSheafPullback_additive (f : X ⟶ Y) :
    (proEtSheafPullback f).Additive :=
  Functor.additive_of_preserves_binary_products (proEtSheafPullback f)

/-- The projection from each base-changed object to the original scheme. -/
noncomputable def proEtBaseChangeProjection (f : X ⟶ Y) :
    proEtBaseChange f ⋙ Scheme.ProEt.forget X ⋙ Over.forget X ⟶
      Scheme.ProEt.forget Y ⋙ Over.forget Y where
  app U := pullback.fst U.hom f
  naturality _U _V _g := pullback.lift_fst _ _ _

/-- The integral coefficient sheaf in the universe used by cohomology. -/
abbrev liftedEllAdicCoefficient (ℓ : ℕ) [Fact ℓ.Prime] (X : Scheme.{u}) :
    Sheaf (Scheme.ProEt.topology X) Ab.{u + 1} :=
  (sheafCompose _ AddCommGrpCat.uliftFunctor.{u + 1}).obj (X.ellAdicSheaf ℓ)

/-- Pullback of coefficient functions along the scheme projections. -/
noncomputable def proEtCoefficientToPushforward (ℓ : ℕ) [Fact ℓ.Prime] (f : X ⟶ Y) :
    liftedEllAdicCoefficient ℓ Y ⟶
      ((proEtBaseChange f).sheafPushforwardContinuous Ab.{u + 1}
        (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X)).obj
          (liftedEllAdicCoefficient ℓ X) where
  hom := Functor.whiskerRight
    (Functor.whiskerRight (NatTrans.op (proEtBaseChangeProjection f))
      (continuousMapPresheafAb (ℤ_[ℓ]))) AddCommGrpCat.uliftFunctor

/-- The adjoint coefficient map to the actual coefficient sheaf on X. -/
noncomputable def proEtCoefficientPullback (ℓ : ℕ) [Fact ℓ.Prime] (f : X ⟶ Y) :
    (proEtSheafPullback f).obj (liftedEllAdicCoefficient ℓ Y) ⟶
      liftedEllAdicCoefficient ℓ X :=
  (((proEtBaseChange f).sheafAdjunctionContinuous Ab.{u + 1}
    (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X)).homEquiv _ _).symm
      (proEtCoefficientToPushforward ℓ f)

/-- Exact inverse image preserves the constant sheaves used to define H. -/
noncomputable def proEtConstantPullbackIso (f : X ⟶ Y) :
    constantSheaf (Scheme.ProEt.topology Y) Ab.{u + 1} ⋙ proEtSheafPullback f ≅
      constantSheaf (Scheme.ProEt.topology X) Ab.{u + 1} :=
  ((constantSheafAdj (Scheme.ProEt.topology Y) Ab.{u + 1}
      (terminalIsTerminal (C := Y.ProEt))).comp
    ((proEtBaseChange f).sheafAdjunctionContinuous Ab.{u + 1}
      (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X))).leftAdjointUniq
    (constantSheafAdj (Scheme.ProEt.topology X) Ab.{u + 1}
      (terminalIsTerminal.isTerminalObj (proEtBaseChange f) (⊤_ Y.ProEt)))

/-- The integer constant sheaf serving as the source of the Ext definition. -/
abbrev proEtIntegerConstant (X : Scheme.{u}) : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1} :=
  (constantSheaf (Scheme.ProEt.topology X) Ab.{u + 1}).obj
    (AddCommGrpCat.of (ULift.{u + 1} ℤ))

/-- Pullback on mathlib's actual integral ℓ-adic cohomology groups. -/
noncomputable def integralEllAdicPullback (ℓ : ℕ) [Fact ℓ.Prime]
    (f : X ⟶ Y) (n : ℕ) : Y.EllAdicCohomology ℓ n →+ X.EllAdicCohomology ℓ n :=
  ((Abelian.Ext.mk₀ (proEtCoefficientPullback ℓ f)).postcomp
      (proEtIntegerConstant X) (add_zero n)).comp
    (((Abelian.Ext.mk₀ ((proEtConstantPullbackIso f).inv.app
        (AddCommGrpCat.of (ULift.{u + 1} ℤ)))).precomp
        ((proEtSheafPullback f).obj (liftedEllAdicCoefficient ℓ Y)) (zero_add n)).comp
      ((proEtSheafPullback f).mapExtAddHom (proEtIntegerConstant Y)
        (liftedEllAdicCoefficient ℓ Y) n))

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.ProetalePullback.Construction
